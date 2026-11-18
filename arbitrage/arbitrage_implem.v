From Arbitrage.spec Require Import Prelude.
From Stdlib Require Import ZArith NArith QArith Qreals List Uint63 PArray Floats Reals Lra Lia ZifyUint63 Zwf.
From Stdlib Require Sint63.
From StdGalilei Require Import repr repr_float.
From Flocq Require Core.Core.
Import ListNotations.

Open Scope uint63_scope.
Unset Lia Cache.

Ltac sia := zify; Z.to_euclidean_division_equations; lia.

(* ------------------------------------------------------------------ *)
(* The termination device and the loop combinator                     *)
(* ------------------------------------------------------------------ *)

Definition bdec (b : bool) : {b = true} + {b = false} :=
  match b as b0 return {b0 = true} + {b0 = false} with
  | true => left eq_refl
  | false => right eq_refl
  end.

Definition gap (m j : int) : Z := (to_Z m - to_Z j)%Z.

Lemma dec_step : forall hi i : int, (i <? hi) = true -> Zwf 0 (gap hi (i + 1)) (gap hi i).
Proof.
  intros hi i H. rewrite Uint63.ltb_spec in H. pose proof (to_Z_bounded hi).
  assert (to_Z (i + 1) = (to_Z i + 1)%Z) by sia. unfold Zwf, gap. lia.
Qed.

Section Loop.
Context {St : Type}.

Fixpoint wloop (hi : int) (cont : int -> St -> bool) (f : int -> St -> St)
    (i : int) (s : St) (H : Acc (Zwf 0) (gap hi i)) {struct H} : St :=
  match bdec (i <? hi) with
  | left Hi =>
      if cont i s then wloop hi cont f (i + 1) (f i s) (Acc_inv H (dec_step hi i Hi))
      else s
  | right _ => s
  end.

Definition loop (hi : int) (cont : int -> St -> bool) (f : int -> St -> St)
    (i : int) (s : St) : St :=
  wloop hi cont f i s (Zwf_well_founded 0 (gap hi i)).

End Loop.

(* ------------------------------------------------------------------ *)
(* The program                                                         *)
(* ------------------------------------------------------------------ *)

(* -- The 25 primes below 100, and the multiplicity of p in n <= 100. *)
Definition primes : array int :=
  (PArray.make 25 0).[0 <- 2].[1 <- 3].[2 <- 5].[3 <- 7].[4 <- 11].[5 <- 13]
    .[6 <- 17].[7 <- 19].[8 <- 23].[9 <- 29].[10 <- 31].[11 <- 37].[12 <- 41]
    .[13 <- 43].[14 <- 47].[15 <- 53].[16 <- 59].[17 <- 61].[18 <- 67]
    .[19 <- 71].[20 <- 73].[21 <- 79].[22 <- 83].[23 <- 89].[24 <- 97].

Definition dvd1 (n x : int) : int := if n mod x =? 0 then 1 else 0.

(* sum over e = 1..6 of [p^e divides n]: the multiplicity, for n <= 100 *)
Definition mlt (n p : int) : int :=
  let p2 := p * p in let p3 := p2 * p in let p4 := p3 * p in
  let p5 := p4 * p in let p6 := p5 * p in
  dvd1 n p + dvd1 n p2 + dvd1 n p3 + dvd1 n p4 + dvd1 n p5 + dvd1 n p6.

(* -- Exact arithmetic (Z), only in the comparison of two prime products. *)
Lemma dec_half : forall i : int, (i =? 0) = false -> Zwf 0 (to_Z (i / 2)) (to_Z i).
Proof.
  intros i H. assert (to_Z i <> 0%Z).
  { intros E. assert (i = 0) by (apply to_Z_inj; exact E). subst i. discriminate. }
  pose proof (to_Z_bounded i). unfold Zwf. sia.
Qed.

Fixpoint zofi_rec (i : int) (H : Acc (Zwf 0) (to_Z i)) {struct H} : Z :=
  match bdec (i =? 0) with
  | left _ => 0%Z
  | right Hn =>
      let r := zofi_rec (i / 2) (Acc_inv H (dec_half i Hn)) in
      let bit := if i mod 2 =? 0 then 0%Z else 1%Z in
      (2 * r + bit)%Z
  end.

Definition zofi (i : int) : Z := zofi_rec i (Zwf_well_founded 0 (to_Z i)).

(* D_t = dv t: accumulate P = prod_{D_t > 0} p_t^D_t and
   Q = prod_{D_t < 0} p_t^(-D_t); nz records a non-zero D_t *)
Definition ex_step (dv : int -> int) (t : int) (s : bool * Z * Z) : bool * Z * Z :=
  let '(nz, P, Q) := s in
  let d := dv t in
  if Sint63.ltb 0 d then (true, (P * Z.pow (zofi primes.[t]) (zofi d))%Z, Q)
  else if Sint63.ltb d 0 then (true, P, (Q * Z.pow (zofi primes.[t]) (zofi (0 - d)))%Z)
  else s.

(* the product of p_t^(dv t) exceeds 1; zero D is equality *)
Definition exact_gt (dv : int -> int) : bool :=
  let '(nz, P, Q) := loop 25 (fun _ _ => true) (ex_step dv) 0 (false, 1%Z, 1%Z) in
  if nz then Z.ltb Q P else false.

(* -- Float pairs: mantissa in [1, 2], biased binary exponent, rounding count. *)
Definition f_one : float := of_uint63 1.
Definition f_two : float := of_uint63 2.
Definition f_c0 : float := of_uint63 1048576.
Definition f_c1 : float := of_uint63 1048577.
Definition cap : int := 1048576.
Definition BIAS : int := 1073741824.

(* the product of two cells, renormalised *)
Definition mulcell (m1 : float) (e1 n1 : int) (m2 : float) (e2 n2 : int)
    : float * int * int :=
  let p := (m1 * m2)%float in
  let n := n1 + n2 + 2 in
  let n' := if cap <? n then cap + 1 else n in
  if (f_two <=? p)%float then ((p / f_two)%float, e1 + e2 - BIAS + 1, n')
  else (p, e1 + e2 - BIAS, n').

(* the rate b / a as a cell: exponent from the leading bits *)
Definition ratecell (a b : int) : float * int * int :=
  let ha := head0 a in
  let hb := head0 b in
  let num := if ha <? hb then b << (hb - ha) else b in
  let den := if ha <? hb then a else a << (ha - hb) in
  let r := (of_uint63 num / of_uint63 den)%float in
  let e := BIAS + ha - hb in
  if (r <? f_one)%float then ((r * f_two)%float, e - 1, 2) else (r, e, 2).

(* the certified float comparison: Some true when cell 1 is surely the
   larger, Some false when surely the smaller, None when too close or a
   rounding count is beyond the cap *)
Definition fcmp (m1 : float) (e1 n1 : int) (m2 : float) (e2 n2 : int) : option bool :=
  if (cap <? n1) || (cap <? n2) then None
  else if e2 + 2 <=? e1 then Some true
  else if e1 + 2 <=? e2 then Some false
  else
    let x := if e2 <? e1 then (m1 * f_two)%float else m1 in
    let y := if e1 <? e2 then (m2 * f_two)%float else m2 in
    if (y * f_c1 <? x * f_c0)%float then Some true
    else if (x * f_c1 <? y * f_c0)%float then Some false
    else None.

(* -- The tables: one flat c*c table per field, 25 cells per vector. *)
Record tabs := mkT {
  tPR : array bool;    (* the cell holds a product *)
  tMA : array float;   (* mantissa *)
  tEX : array int;     (* biased exponent *)
  tCN : array int;     (* rounding count *)
  tVT : array int      (* exponent vector, at 25 * cell + t *)
}.

Definition wr_head (T : tabs) (q : int) (m : float) (e n : int) (V : array int) : tabs :=
  mkT (tPR T).[q <- true] (tMA T).[q <- m] (tEX T).[q <- e] (tCN T).[q <- n] V.

Definition vadd (bd b1 b2 : int) (V : array int) : array int :=
  loop 25 (fun _ _ => true) (fun t W => W.[bd + t <- W.[b1 + t] + W.[b2 + t]]) 0 V.

Definition vset (bd a b : int) (V : array int) : array int :=
  loop 25 (fun _ _ => true)
    (fun t W => W.[bd + t <- mlt b primes.[t] - mlt a primes.[t]]) 0 V.

(* -- The initial table: the best rate per ordered pair. *)
Definition init_step (c : int) (xs xd xa xb : array int) (r : int) (T : tabs) : tabs :=
  let u := xs.[r] in let v := xd.[r] in let a := xa.[r] in let b := xb.[r] in
  let q := u * c + v in
  let '(m, e, n) := ratecell a b in
  let better :=
    if (tPR T).[q] then
      match fcmp m e n (tMA T).[q] (tEX T).[q] (tCN T).[q] with
      | Some g => g
      | None => exact_gt (fun t => mlt b primes.[t] - mlt a primes.[t] - (tVT T).[25 * q + t])
      end
    else true in
  if better then wr_head T q m e n (vset (25 * q) a b (tVT T)) else T.

(* -- Floyd-Warshall in (max, x), in place, early exit on the diagonal. *)
Definition fw_j (c k i : int) (j : int) (s : tabs * bool) : tabs * bool :=
  let T := fst s in
  if j =? k then s else
  let qkj := k * c + j in
  if (tPR T).[qkj] then
    let qik := i * c + k in
    let qij := i * c + j in
    let '(m, e, n) := mulcell (tMA T).[qik] (tEX T).[qik] (tCN T).[qik]
                              (tMA T).[qkj] (tEX T).[qkj] (tCN T).[qkj] in
    let bik := 25 * qik in let bkj := 25 * qkj in let bij := 25 * qij in
    let ex :=
      if i =? j then
        match fcmp m e n f_one BIAS 0 with
        | Some g => g
        | None => exact_gt (fun t => (tVT T).[bik + t] + (tVT T).[bkj + t])
        end
      else false in
    if ex then (T, true) else
    let better :=
      if (tPR T).[qij] then
        match fcmp m e n (tMA T).[qij] (tEX T).[qij] (tCN T).[qij] with
        | Some g => g
        | None => exact_gt (fun t => (tVT T).[bik + t] + (tVT T).[bkj + t] - (tVT T).[bij + t])
        end
      else true in
    if better then (wr_head T qij m e n (vadd bij bik bkj (tVT T)), false) else s
  else s.

Definition fw_i (c k : int) (i : int) (s : tabs * bool) : tabs * bool :=
  if i =? k then s else
  if (tPR (fst s)).[i * c + k] then loop c (fun _ s => negb (snd s)) (fw_j c k i) 0 s
  else s.

Definition fw_k (c : int) (k : int) (s : tabs * bool) : tabs * bool :=
  loop c (fun _ s => negb (snd s)) (fw_i c k) 0 s.

Definition arbitrage_impl (c : uint) (xs xd xa xb : array uint) : bool :=
  let cc := c * c in
  let T0 := mkT (PArray.make cc false) (PArray.make cc f_one) (PArray.make cc 0)
                (PArray.make cc 0) (PArray.make (25 * cc) 0) in
  let T1 := loop (PArray.length xs) (fun _ _ => true) (init_step c xs xd xa xb) 0 T0 in
  snd (loop c (fun _ s => negb (snd s)) (fw_k c) 0 (T1, false)).

(* ================================================================== *)
(* Part B: walks and the Floyd-Warshall invariant, on the math side    *)
(* ================================================================== *)

Notation lget := Prelude.get.

Section Walks.
Local Open Scope N_scope.
Variables (src dst a b : list N) (c : N).

Definition walk (u v : N) (ks : list N) : Prop :=
  leads src dst u v ks /\ Forall (fun k => k < len src) ks.
Definition verts (ks : list N) : list N := map (lget dst) ks.
Definition inter (ks : list N) : list N := removelast (verts ks).
Definition below (k : N) (l : list N) : Prop := Forall (fun v => v < k) l.
Definition simple (u v : N) (ks : list N) : Prop :=
  NoDup (inter ks) /\ ~ In u (inter ks) /\ ~ In v (inter ks).
Definition rt (k : N) : R := (IZR (Z.of_N (lget b k)) / IZR (Z.of_N (lget a k)))%R.
Definition wprod (ks : list N) : R := fold_right (fun k acc => (rt k * acc)%R) 1%R ks.

Lemma leads_app : forall l1 l2 u v,
  leads src dst u v (l1 ++ l2) <-> exists m, leads src dst u m l1 /\ leads src dst m v l2.
Proof.
  induction l1 as [| k l1 IH]; intros l2 u v; simpl.
  - split; [intros H; exists u; auto | intros (m & -> & H); exact H].
  - rewrite IH. split.
    + intros (Hk & m & H1 & H2). exists m. auto.
    + intros (m & (Hk & H1) & H2). split; [exact Hk | exists m; auto].
Qed.

Lemma walk_app : forall l1 l2 u m v,
  walk u m l1 -> walk m v l2 -> walk u v (l1 ++ l2).
Proof.
  intros l1 l2 u m v [H1 F1] [H2 F2]. split.
  - apply leads_app. exists m. auto.
  - apply Forall_app. auto.
Qed.

Lemma walk_app_inv : forall l1 l2 u v, walk u v (l1 ++ l2) ->
  exists m, walk u m l1 /\ walk m v l2.
Proof.
  intros l1 l2 u v [H F]. apply leads_app in H as (m & H1 & H2).
  apply Forall_app in F as [F1 F2]. exists m. split; split; auto.
Qed.

Lemma verts_last : forall ks u v, leads src dst u v ks -> ks <> [] ->
  verts ks = inter ks ++ [v].
Proof.
  induction ks as [| k ks IH]; intros u v H Hne; [congruence |].
  destruct ks as [| k' ks'].
  - destruct H as [_ H]. simpl in H. unfold inter, verts. simpl. rewrite H. reflexivity.
  - destruct H as [_ H]. unfold inter. simpl verts.
    change (removelast (lget dst k :: verts (k' :: ks')))
      with (lget dst k :: removelast (verts (k' :: ks'))).
    simpl. f_equal. apply (IH _ _ H). discriminate.
Qed.

Lemma inter_app : forall l1 l2 u m, leads src dst u m l1 -> l1 <> [] -> l2 <> [] ->
  inter (l1 ++ l2) = inter l1 ++ m :: inter l2.
Proof.
  intros l1 l2 u m H N1 N2. unfold inter at 1. unfold verts at 1. rewrite map_app.
  fold (verts l1). fold (verts l2).
  rewrite (verts_last l1 u m H N1), <- app_assoc, removelast_app.
  - f_equal. unfold inter.
    destruct (verts l2) eqn:Ev; [destruct l2; simpl in Ev; congruence | reflexivity].
  - discriminate.
Qed.

Lemma inter_nil : forall ks, ks <> [] -> inter ks = [] -> exists k, ks = [k].
Proof.
  intros [| k [| k' ks]] H1 H2; [congruence | eauto |].
  unfold inter in H2. simpl in H2. discriminate.
Qed.

Lemma inter_single : forall k, inter [k] = [].
Proof. reflexivity. Qed.

Lemma length_inter : forall ks, List.length (inter ks) = (List.length ks - 1)%nat.
Proof.
  intros ks. unfold inter. destruct ks as [| k ks]; [reflexivity |].
  assert (Hn : verts (k :: ks) <> []) by discriminate.
  pose proof (app_removelast_last 0 Hn) as E.
  apply (f_equal (@List.length N)) in E. rewrite length_app in E. simpl in E.
  unfold verts in E at 1. rewrite length_map in E. simpl in *. lia.
Qed.

(* first interior occurrence of v *)
Lemma split_first : forall ks u w v, leads src dst u w ks -> In v (inter ks) ->
  exists l1 l2, ks = l1 ++ l2 /\ l1 <> [] /\ l2 <> [] /\
    leads src dst u v l1 /\ leads src dst v w l2 /\ ~ In v (inter l1).
Proof.
  induction ks as [| k ks IH]; intros u w v H Hin; [destruct Hin |].
  destruct ks as [| k' ks']; [destruct Hin |].
  destruct H as [Hk H].
  unfold inter in Hin. simpl verts in Hin.
  change (removelast (lget dst k :: verts (k' :: ks')))
    with (lget dst k :: removelast (verts (k' :: ks'))) in Hin.
  destruct (N.eq_dec (lget dst k) v) as [E | E].
  - exists [k], (k' :: ks').
    split; [reflexivity |]. split; [discriminate |]. split; [discriminate |].
    split; [split; [exact Hk | exact E] |].
    split; [rewrite <- E; exact H |].
    rewrite inter_single. simpl. auto.
  - destruct Hin as [Hin | Hin]; [congruence |].
    destruct (IH _ _ _ H Hin) as (l1 & l2 & -> & N1 & N2 & H1 & H2 & Hn).
    exists (k :: l1), l2.
    split; [reflexivity |]. split; [discriminate |]. split; [exact N2 |].
    split; [split; [exact Hk | exact H1] |]. split; [exact H2 |].
    change (k :: l1) with ([k] ++ l1).
    rewrite (inter_app [k] l1 u (lget dst k)) by (simpl; auto; discriminate).
    simpl. intros [F | F]; auto.
Qed.

Lemma split_inter : forall l1 l2 u m, leads src dst u m l1 -> l1 <> [] -> l2 <> [] ->
  forall v, (In v (inter l1) \/ In v (inter l2) \/ v = m) -> In v (inter (l1 ++ l2)).
Proof.
  intros l1 l2 u m H N1 N2 v Hv. rewrite (inter_app l1 l2 u m H N1 N2).
  apply in_or_app. simpl. destruct Hv as [Hv | [Hv | Hv]]; auto.
Qed.

Lemma wprod_app : forall l1 l2, wprod (l1 ++ l2) = (wprod l1 * wprod l2)%R.
Proof.
  induction l1 as [| k l1 IH]; intros l2; simpl; [ring | rewrite IH; ring].
Qed.

Lemma rt_nonneg : forall k, (0 <= rt k)%R.
Proof.
  intros k. unfold rt. unfold Rdiv. apply Rmult_le_pos.
  - apply IZR_le. lia.
  - destruct (Z.eq_dec (Z.of_N (lget a k)) 0) as [E | E].
    + rewrite E, Rinv_0. lra.
    + apply Rlt_le, Rinv_0_lt_compat, IZR_lt. lia.
Qed.

Lemma wprod_nonneg : forall ks, (0 <= wprod ks)%R.
Proof.
  induction ks as [| k ks IH]; simpl; [lra |].
  apply Rmult_le_pos; [apply rt_nonneg | exact IH].
Qed.

Lemma below_succ : forall k l, below (k + 1) l -> ~ In k l -> below k l.
Proof.
  intros k l H Hn. unfold below in *. rewrite Forall_forall in *.
  intros v Hv. specialize (H v Hv). assert (v <> k) by (intros ->; auto). lia.
Qed.

Lemma below_mono : forall k k' l, k <= k' -> below k l -> below k' l.
Proof.
  intros k k' l Hk H. unfold below in *. rewrite Forall_forall in *.
  intros v Hv. specialize (H v Hv). lia.
Qed.

Lemma below_incl : forall k l l', (forall v, In v l -> In v l') -> below k l' -> below k l.
Proof.
  intros k l l' Hi H. unfold below in *. rewrite Forall_forall in *. auto.
Qed.

(* -- the abstract table and its invariant at stage k ------------------ *)

Definition IS (k : N) (D : N -> N -> option (list N)) : Prop :=
  forall x y w, D x y = Some w ->
    walk x y w /\ w <> [] /\ simple x y w /\ below k (inter w).
Definition IC (k : N) (D : N -> N -> option (list N)) : Prop :=
  forall x y W, walk x y W -> W <> [] -> below k (inter W) ->
    exists w, D x y = Some w /\ (wprod W <= wprod w)%R.
Definition ID (D : N -> N -> option (list N)) : Prop :=
  forall x w, D x x = Some w -> (wprod w <= 1)%R.

Definition better (w : list N) (o : option (list N)) : bool :=
  match o with
  | None => true
  | Some w0 => if Rlt_dec (wprod w0) (wprod w) then true else false
  end.

Definition upd (k : N) (D : N -> N -> option (list N)) (x y : N) : option (list N) :=
  if N.eqb x k || N.eqb y k then D x y else
  match D x k, D k y with
  | Some w1, Some w2 => if better (w1 ++ w2) (D x y) then Some (w1 ++ w2) else D x y
  | _, _ => D x y
  end.

Definition noexit (k : N) (D : N -> N -> option (list N)) : Prop :=
  forall x w1 w2, x <> k -> D x k = Some w1 -> D k x = Some w2 ->
    (wprod (w1 ++ w2) <= 1)%R.

Lemma upd_ge : forall k D x y w, D x y = Some w ->
  exists w', upd k D x y = Some w' /\ (wprod w <= wprod w')%R.
Proof.
  intros k D x y w H. unfold upd.
  destruct (N.eqb x k || N.eqb y k); [exists w; split; [exact H | lra] |].
  destruct (D x k) as [w1 |], (D k y) as [w2 |]; try (exists w; split; [exact H | lra]).
  rewrite H. unfold better. destruct (Rlt_dec (wprod w) (wprod (w1 ++ w2))) as [L | L].
  - exists (w1 ++ w2). split; [reflexivity | lra].
  - exists w. split; [reflexivity | lra].
Qed.

Section Stage.
Variables (k : N) (D : N -> N -> option (list N)).
Hypotheses (HS : IS k D) (HC : IC k D) (HD : ID D).

Lemma lemA : forall n W x, (List.length W <= n)%nat -> walk x k W -> W <> [] ->
  below (k + 1) (inter W) -> exists w, D x k = Some w /\ (wprod W <= wprod w)%R.
Proof.
  induction n as [| n IH]; intros W x Hl Hw Hne Hb.
  - destruct W; simpl in Hl; [congruence | lia].
  - destruct (in_dec N.eq_dec k (inter W)) as [Hin | Hin].
    + destruct Hw as [Hlw Hf].
      destruct (split_first W x k k Hlw Hin) as (l1 & l2 & -> & N1 & N2 & H1 & H2 & Hn).
      apply Forall_app in Hf as [F1 F2].
      assert (Hsub : forall v, In v (inter l1) \/ In v (inter l2) \/ v = k ->
                In v (inter (l1 ++ l2))) by (apply (split_inter _ _ x k H1 N1 N2)).
      destruct (HC x k l1) as (w & Ew & Le1).
      { split; auto. }
      { exact N1. }
      { apply below_succ; [| exact Hn].
        apply (below_incl _ _ (inter (l1 ++ l2))); [intros v Hv; apply Hsub; auto | exact Hb]. }
      destruct (IH l2 k) as (w' & Ew' & Le2).
      { rewrite length_app in Hl. destruct l1; [congruence | simpl in Hl; lia]. }
      { split; auto. }
      { exact N2. }
      { apply (below_incl _ _ (inter (l1 ++ l2))); [intros v Hv; apply Hsub; auto | exact Hb]. }
      exists w. split; [exact Ew |].
      pose proof (HD _ _ Ew'). rewrite wprod_app.
      pose proof (wprod_nonneg l1). pose proof (wprod_nonneg l2).
      replace (wprod w) with (wprod w * 1)%R by ring.
      apply Rmult_le_compat; lra.
    + apply HC; auto. apply below_succ; auto.
Qed.

Lemma lemB : forall n W y, (List.length W <= n)%nat -> walk k y W -> W <> [] ->
  below (k + 1) (inter W) -> exists w, D k y = Some w /\ (wprod W <= wprod w)%R.
Proof.
  induction n as [| n IH]; intros W y Hl Hw Hne Hb.
  - destruct W; simpl in Hl; [congruence | lia].
  - destruct (in_dec N.eq_dec k (inter W)) as [Hin | Hin].
    + destruct Hw as [Hlw Hf].
      destruct (split_first W k y k Hlw Hin) as (l1 & l2 & -> & N1 & N2 & H1 & H2 & Hn).
      apply Forall_app in Hf as [F1 F2].
      assert (Hsub : forall v, In v (inter l1) \/ In v (inter l2) \/ v = k ->
                In v (inter (l1 ++ l2))) by (apply (split_inter _ _ k k H1 N1 N2)).
      destruct (HC k k l1) as (w & Ew & Le1).
      { split; auto. }
      { exact N1. }
      { apply below_succ; [| exact Hn].
        apply (below_incl _ _ (inter (l1 ++ l2))); [intros v Hv; apply Hsub; auto | exact Hb]. }
      destruct (IH l2 y) as (w' & Ew' & Le2).
      { rewrite length_app in Hl. destruct l1; [congruence | simpl in Hl; lia]. }
      { split; auto. }
      { exact N2. }
      { apply (below_incl _ _ (inter (l1 ++ l2))); [intros v Hv; apply Hsub; auto | exact Hb]. }
      exists w'. split; [exact Ew' |].
      pose proof (HD _ _ Ew). rewrite wprod_app.
      pose proof (wprod_nonneg l1). pose proof (wprod_nonneg l2).
      replace (wprod w') with (1 * wprod w')%R by ring.
      apply Rmult_le_compat; lra.
    + apply HC; auto. apply below_succ; auto.
Qed.

Lemma IC_step : IC (k + 1) (upd k D).
Proof.
  intros x y W Hw Hne Hb.
  destruct (in_dec N.eq_dec k (inter W)) as [Hin | Hin].
  - destruct Hw as [Hlw Hf].
    destruct (split_first W x y k Hlw Hin) as (l1 & l2 & -> & N1 & N2 & H1 & H2 & Hn).
    apply Forall_app in Hf as [F1 F2].
    assert (Hsub : forall v, In v (inter l1) \/ In v (inter l2) \/ v = k ->
              In v (inter (l1 ++ l2))) by (apply (split_inter _ _ x k H1 N1 N2)).
    assert (Hb1 : below k (inter l1)).
    { apply below_succ; [| exact Hn].
      apply (below_incl _ _ (inter (l1 ++ l2))); [intros v Hv; apply Hsub; auto | exact Hb]. }
    assert (Hb2 : below (k + 1) (inter l2)).
    { apply (below_incl _ _ (inter (l1 ++ l2))); [intros v Hv; apply Hsub; auto | exact Hb]. }
    destruct (HC x k l1) as (w1 & E1 & Le1); [split; auto | exact N1 | exact Hb1 |].
    destruct (lemB (List.length l2) l2 y (Nat.le_refl _)) as (w2 & E2 & Le2);
      [split; auto | exact N2 | exact Hb2 |].
    pose proof (wprod_nonneg l1). pose proof (wprod_nonneg l2).
    rewrite wprod_app.
    unfold upd.
    destruct (N.eqb_spec x k) as [Ex | Ex].
    + subst x. simpl. exists w2. split; [exact E2 |].
      pose proof (HD _ _ E1). replace (wprod w2) with (1 * wprod w2)%R by ring.
      apply Rmult_le_compat; lra.
    + destruct (N.eqb_spec y k) as [Ey | Ey].
      * subst y. simpl.
        destruct (lemA (List.length (l1 ++ l2)) (l1 ++ l2) x (Nat.le_refl _)) as (w & Ew & Le);
          [split; [apply leads_app; exists k; auto | apply Forall_app; auto] | | exact Hb |].
        { destruct l1; [congruence | discriminate]. }
        exists w. split; [exact Ew | rewrite wprod_app in Le; exact Le].
      * simpl. rewrite E1, E2.
        assert (Hp : (wprod l1 * wprod l2 <= wprod (w1 ++ w2))%R).
        { rewrite wprod_app. apply Rmult_le_compat; lra. }
        unfold better. destruct (D x y) as [w0 |].
        -- destruct (Rlt_dec (wprod w0) (wprod (w1 ++ w2))) as [L | L].
           ++ exists (w1 ++ w2). split; [reflexivity | exact Hp].
           ++ exists w0. split; [reflexivity | lra].
        -- exists (w1 ++ w2). split; [reflexivity | exact Hp].
  - destruct (HC x y W Hw Hne) as (w & Ew & Le); [apply below_succ; auto |].
    destruct (upd_ge k D x y w Ew) as (w' & Ew' & Le'). exists w'. split; [exact Ew' | lra].
Qed.

Lemma ID_step : noexit k D -> ID (upd k D).
Proof.
  intros Hne x w Hw. unfold upd in Hw.
  destruct (N.eqb_spec x k) as [Ex | Ex]; [simpl in Hw; apply (HD x); exact Hw |].
  simpl in Hw.
  destruct (D x k) as [w1 |] eqn:E1; [| apply (HD x); exact Hw].
  destruct (D k x) as [w2 |] eqn:E2; [| apply (HD x); exact Hw].
  destruct (better (w1 ++ w2) (D x x)).
  - injection Hw as <-. apply (Hne x); auto.
  - apply (HD x); exact Hw.
Qed.

Lemma IS_step : noexit k D -> IS (k + 1) (upd k D).
Proof.
  intros Hne.
  pose proof IC_step as HC1. pose proof (ID_step Hne) as HD1.
  intros x y w Hw. unfold upd in Hw.
  destruct (N.eqb_spec x k) as [Ex | Ex].
  { destruct (HS _ _ _ Hw) as (? & ? & ? & ?).
    split; [auto | split; [auto | split; [auto | apply (below_mono k); [lia | auto]]]]. }
  destruct (N.eqb_spec y k) as [Ey | Ey].
  { destruct (HS _ _ _ Hw) as (? & ? & ? & ?).
    split; [auto | split; [auto | split; [auto | apply (below_mono k); [lia | auto]]]]. }
  simpl in Hw.
  destruct (D x k) as [w1 |] eqn:E1;
    [| destruct (HS _ _ _ Hw) as (? & ? & ? & ?);
       split; [auto | split; [auto | split; [auto | apply (below_mono k); [lia | auto]]]]].
  destruct (D k y) as [w2 |] eqn:E2;
    [| destruct (HS _ _ _ Hw) as (? & ? & ? & ?);
       split; [auto | split; [auto | split; [auto | apply (below_mono k); [lia | auto]]]]].
  destruct (better (w1 ++ w2) (D x y)) eqn:Eb;
    [| destruct (HS _ _ _ Hw) as (? & ? & ? & ?);
       split; [auto | split; [auto | split; [auto | apply (below_mono k); [lia | auto]]]]].
  injection Hw as <-.
  destruct (HS _ _ _ E1) as (Hw1 & N1 & [Nd1 [Sx1 Sk1]] & B1).
  destruct (HS _ _ _ E2) as (Hw2 & N2 & [Nd2 [Sk2 Sy2]] & B2).
  pose proof (inter_app w1 w2 x k (proj1 Hw1) N1 N2) as Ei.
  assert (Hw12 : walk x y (w1 ++ w2)) by (eapply walk_app; eauto).
  assert (N12 : w1 ++ w2 <> []) by (destruct w1; [congruence | discriminate]).
  (* the strict improvement over every walk below k *)
  assert (Hbet : forall W, walk x y W -> W <> [] -> below k (inter W) ->
             (wprod W < wprod (w1 ++ w2))%R).
  { intros W HW NW BW. destruct (HC x y W HW NW BW) as (w0 & E0 & Le0).
    rewrite E0 in Eb. simpl in Eb.
    destruct (Rlt_dec (wprod w0) (wprod (w1 ++ w2))); [lra | discriminate]. }
  (* a closed walk through k is worth at most 1 *)
  assert (Hcyc : forall v Cy, walk v v Cy -> Cy <> [] -> below (k + 1) (inter Cy) ->
             (wprod Cy <= 1)%R).
  { intros v Cy H1 H2 H3. destruct (HC1 v v Cy H1 H2 H3) as (w' & E' & Le').
    pose proof (HD1 v w' E'). lra. }
  assert (Bk1 : below k (inter w1)) by exact B1.
  assert (Bk2 : below k (inter w2)) by exact B2.
  assert (Kn1 : ~ In k (inter w1)).
  { intros F. unfold below in Bk1. rewrite Forall_forall in Bk1. specialize (Bk1 k F). lia. }
  assert (Kn2 : ~ In k (inter w2)).
  { intros F. unfold below in Bk2. rewrite Forall_forall in Bk2. specialize (Bk2 k F). lia. }
  (* the three ways P1 ++ P2 could repeat a vertex all contradict Hbet *)
  assert (Key : forall v, (v = x /\ In v (inter w2)) \/ (In v (inter w1) /\ v = y) \/
                          (In v (inter w1) /\ In v (inter w2)) -> False).
  { intros v Hv.
    pose proof (wprod_nonneg w1). pose proof (wprod_nonneg w2).
    destruct Hv as [[-> Hi2] | [[Hi1 ->] | [Hi1 Hi2]]].
    - destruct (split_first w2 k y x (proj1 Hw2) Hi2) as (C & E & -> & NC & NE & HC' & HE & _).
      destruct Hw2 as [_ Fw2]. apply Forall_app in Fw2 as [FC FE].
      pose proof (split_inter C E k x HC' NC NE) as Sub.
      assert (L1 : (wprod E < wprod (w1 ++ C ++ E))%R).
      { apply Hbet; [split; auto | exact NE |].
        apply (below_incl _ _ (inter (C ++ E))); [intros v Hv; apply Sub; auto | exact Bk2]. }
      assert (L2 : (wprod (w1 ++ C) <= 1)%R).
      { apply (Hcyc x); [eapply walk_app; [exact Hw1 | split; auto] |
                         destruct w1; [congruence | discriminate] |].
        rewrite (inter_app w1 C x k (proj1 Hw1) N1 NC).
        unfold below. apply Forall_app. split.
        - apply (below_mono k); [lia | exact Bk1].
        - constructor; [lia |]. apply (below_mono k); [lia |].
          apply (below_incl _ _ (inter (C ++ E))); [intros v Hv; apply Sub; auto | exact Bk2]. }
      rewrite app_assoc, wprod_app in L1.
      pose proof (wprod_nonneg (w1 ++ C)). pose proof (wprod_nonneg E).
      assert (wprod (w1 ++ C) * wprod E <= 1 * wprod E)%R by (apply Rmult_le_compat; lra).
      lra.
    - destruct (split_first w1 x k y (proj1 Hw1) Hi1) as (A & B & -> & NA & NB & HA & HB & _).
      destruct Hw1 as [_ Fw1]. apply Forall_app in Fw1 as [FA FB].
      pose proof (split_inter A B x y HA NA NB) as Sub.
      assert (L1 : (wprod A < wprod ((A ++ B) ++ w2))%R).
      { apply Hbet; [split; auto | exact NA |].
        apply (below_incl _ _ (inter (A ++ B))); [intros v Hv; apply Sub; auto | exact Bk1]. }
      assert (L2 : (wprod (B ++ w2) <= 1)%R).
      { apply (Hcyc y); [eapply walk_app; [split; [exact HB | exact FB] | exact Hw2] |
                         destruct B; [congruence | discriminate] |].
        rewrite (inter_app B w2 y k HB NB N2).
        unfold below. apply Forall_app. split.
        - apply (below_mono k); [lia |].
          apply (below_incl _ _ (inter (A ++ B))); [intros v Hv; apply Sub; auto | exact Bk1].
        - constructor; [lia |]. apply (below_mono k); [lia | exact Bk2]. }
      rewrite <- app_assoc, wprod_app in L1.
      pose proof (wprod_nonneg A). pose proof (wprod_nonneg (B ++ w2)).
      assert (wprod A * wprod (B ++ w2) <= wprod A * 1)%R by (apply Rmult_le_compat; lra).
      lra.
    - destruct (split_first w1 x k v (proj1 Hw1) Hi1) as (A & B & -> & NA & NB & HA & HB & _).
      destruct (split_first w2 k y v (proj1 Hw2) Hi2) as (C & E & -> & NC & NE & HC' & HE & _).
      destruct Hw1 as [_ Fw1]. apply Forall_app in Fw1 as [FA FB].
      destruct Hw2 as [_ Fw2]. apply Forall_app in Fw2 as [FC FE].
      pose proof (split_inter A B x v HA NA NB) as Sub1.
      pose proof (split_inter C E k v HC' NC NE) as Sub2.
      assert (Bv : v < k).
      { unfold below in Bk1. rewrite Forall_forall in Bk1. apply Bk1. exact Hi1. }
      assert (L1 : (wprod (A ++ E) < wprod ((A ++ B) ++ C ++ E))%R).
      { apply Hbet; [eapply walk_app; split; eauto | destruct A; [congruence | discriminate] |].
        rewrite (inter_app A E x v HA NA NE). unfold below. apply Forall_app. split.
        - apply (below_incl _ _ (inter (A ++ B))); [intros v' Hv'; apply Sub1; auto | exact Bk1].
        - constructor; [exact Bv |].
          apply (below_incl _ _ (inter (C ++ E))); [intros v' Hv'; apply Sub2; auto | exact Bk2]. }
      assert (L2 : (wprod (B ++ C) <= 1)%R).
      { apply (Hcyc v); [eapply walk_app; split; eauto | destruct B; [congruence | discriminate] |].
        rewrite (inter_app B C v k HB NB NC). unfold below. apply Forall_app. split.
        - apply (below_mono k); [lia |].
          apply (below_incl _ _ (inter (A ++ B))); [intros v' Hv'; apply Sub1; auto | exact Bk1].
        - constructor; [lia |]. apply (below_mono k); [lia |].
          apply (below_incl _ _ (inter (C ++ E))); [intros v' Hv'; apply Sub2; auto | exact Bk2]. }
      rewrite !wprod_app in L1, L2.
      pose proof (wprod_nonneg A). pose proof (wprod_nonneg B).
      pose proof (wprod_nonneg C). pose proof (wprod_nonneg E).
      assert (wprod A * wprod E * (wprod B * wprod C) <= wprod A * wprod E * 1)%R
        by (apply Rmult_le_compat_l; [apply Rmult_le_pos |]; lra).
      assert (wprod ((A ++ B) ++ C ++ E) = wprod A * wprod E * (wprod B * wprod C))%R
        by (rewrite !wprod_app; ring).
      lra. }
  split; [exact Hw12 |]. split; [exact N12 |]. split; [split; [| split] |].
  - rewrite Ei. apply NoDup_app; auto.
    + constructor; auto.
    + intros v Hv1 Hv2. destruct Hv2 as [<- | Hv2]; [contradiction |].
      apply (Key v). auto.
  - rewrite Ei. intros F. apply in_app_or in F as [F | [F | F]].
    + contradiction.
    + congruence.
    + apply (Key x). auto.
  - rewrite Ei. intros F. apply in_app_or in F as [F | [F | F]].
    + apply (Key y). auto.
    + congruence.
    + contradiction.
  - rewrite Ei. unfold below. apply Forall_app. split.
    + apply (below_mono k); [lia | exact Bk1].
    + constructor; [lia |]. apply (below_mono k); [lia | exact Bk2].
Qed.

End Stage.

End Walks.

(* ================================================================== *)
(* Part C: exponent vectors over the 25 primes, and the exact oracle   *)
(* ================================================================== *)

Definition plist : list Z :=
  [2; 3; 5; 7; 11; 13; 17; 19; 23; 29; 31; 37; 41; 43; 47; 53; 59; 61; 67; 71;
   73; 79; 83; 89; 97]%Z.
Definition pZ (t : nat) : Z := nth t plist 0%Z.

Definition dvdZ (n x : Z) : Z := if Z.eqb (n mod x) 0 then 1 else 0.
Definition mZ (n p : Z) : Z :=
  (dvdZ n p + dvdZ n (p ^ 2) + dvdZ n (p ^ 3) + dvdZ n (p ^ 4) + dvdZ n (p ^ 5)
   + dvdZ n (p ^ 6))%Z.

Fixpoint prodZ (n : nat) (g : nat -> Z) : Z :=
  match n with O => 1%Z | S n => (prodZ n g * g n)%Z end.
Fixpoint prodR (n : nat) (g : nat -> R) : R :=
  match n with O => 1%R | S n => (prodR n g * g n)%R end.

Definition Zfac (n : Z) : Z := prodZ 25 (fun t => pZ t ^ mZ n (pZ t))%Z.

Lemma Zfac_check :
  forallb (fun n => Z.eqb (Zfac (Z.of_nat n)) (Z.of_nat n)) (seq 1 100) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma Zfac_ok : forall n : Z, (1 <= n <= 100)%Z -> Zfac n = n.
Proof.
  intros n Hn. pose proof Zfac_check as H. rewrite forallb_forall in H.
  specialize (H (Z.to_nat n)). rewrite Z2Nat.id in H by lia.
  apply Z.eqb_eq, H, in_seq. lia.
Qed.

Lemma pZ_bound : forall t, (t < 25)%nat -> (2 <= pZ t <= 97)%Z.
Proof.
  intros t Ht. do 25 (destruct t as [| t]; [unfold pZ; simpl; lia |]). lia.
Qed.

Lemma mZ_bound : forall n p, (0 <= mZ n p <= 6)%Z.
Proof.
  intros n p. unfold mZ, dvdZ.
  repeat match goal with |- context [Z.eqb ?x ?y] => destruct (Z.eqb x y) end; lia.
Qed.

(* the real a vector denotes: prod_t p_t ^ f t *)
Definition Vp (f : nat -> Z) : R := prodR 25 (fun t => powerRZ (IZR (pZ t)) (f t)).

Lemma prodR_pos : forall n g, (forall t, (t < n)%nat -> (0 < g t)%R) -> (0 < prodR n g)%R.
Proof.
  induction n as [| n IH]; intros g H; simpl; [lra |].
  apply Rmult_lt_0_compat; [apply IH; intros; apply H; lia | apply H; lia].
Qed.

Lemma prodR_mul : forall n g h, prodR n (fun t => g t * h t)%R = (prodR n g * prodR n h)%R.
Proof. induction n as [| n IH]; intros g h; simpl; [ring | rewrite IH; ring]. Qed.

Lemma prodR_ext : forall n g h, (forall t, (t < n)%nat -> g t = h t) -> prodR n g = prodR n h.
Proof.
  induction n as [| n IH]; intros g h H; simpl; [reflexivity |].
  rewrite (IH g h) by (intros; apply H; lia). rewrite H by lia. reflexivity.
Qed.

Lemma pR_pos : forall t, (t < 25)%nat -> (0 < IZR (pZ t))%R.
Proof. intros t Ht. apply IZR_lt. pose proof (pZ_bound t Ht). lia. Qed.

Lemma Vp_pos : forall f, (0 < Vp f)%R.
Proof. intros f. apply prodR_pos. intros t Ht. apply powerRZ_lt, pR_pos, Ht. Qed.

Lemma Vp_ext : forall f g, (forall t, (t < 25)%nat -> f t = g t) -> Vp f = Vp g.
Proof. intros f g H. apply prodR_ext. intros t Ht. rewrite H by exact Ht. reflexivity. Qed.

Lemma Vp_add : forall f g, Vp (fun t => f t + g t)%Z = (Vp f * Vp g)%R.
Proof.
  intros f g. unfold Vp. rewrite <- prodR_mul. apply prodR_ext. intros t Ht.
  apply powerRZ_add. pose proof (pR_pos t Ht). lra.
Qed.

Lemma Vp_opp : forall f, Vp (fun t => - f t)%Z = (/ Vp f)%R.
Proof.
  intros f. unfold Vp.
  assert (G : forall n, (n <= 25)%nat ->
    prodR n (fun t => powerRZ (IZR (pZ t)) (- f t)) =
    (/ prodR n (fun t => powerRZ (IZR (pZ t)) (f t)))%R).
  { induction n as [| n IH]; intros Hn; simpl; [lra |].
    rewrite IH by lia. rewrite powerRZ_neg'.
    rewrite Rinv_mult. reflexivity. }
  apply G. lia.
Qed.

Lemma Vp_sub : forall f g, Vp (fun t => f t - g t)%Z = (Vp f / Vp g)%R.
Proof.
  intros f g. unfold Rdiv. rewrite <- Vp_opp, <- Vp_add.
  apply Vp_ext. intros t _. lia.
Qed.

Lemma Vp_zero : Vp (fun _ => 0%Z) = 1%R.
Proof. unfold Vp. simpl. ring. Qed.

Lemma IZR_pow_powerRZ : forall p e, (0 <= e)%Z -> IZR (p ^ e) = powerRZ (IZR p) e.
Proof.
  intros p e He. rewrite <- (Z2Nat.id e He) at 2. rewrite <- pow_powerRZ, pow_IZR.
  rewrite Z2Nat.id by exact He. reflexivity.
Qed.

Lemma Vp_mZ : forall n, (1 <= n <= 100)%Z -> Vp (fun t => mZ n (pZ t)) = IZR n.
Proof.
  intros n Hn. transitivity (IZR (Zfac n)); [| rewrite Zfac_ok by exact Hn; reflexivity].
  unfold Vp, Zfac.
  assert (G : forall m, IZR (prodZ m (fun t => pZ t ^ mZ n (pZ t))%Z) =
                        prodR m (fun t => powerRZ (IZR (pZ t)) (mZ n (pZ t)))).
  { induction m as [| m IH]; simpl; [reflexivity |].
    rewrite mult_IZR, IH, IZR_pow_powerRZ; [reflexivity |].
    pose proof (mZ_bound n (pZ m)). lia. }
  symmetry. apply G.
Qed.

(* -- the oracle's exact path ------------------------------------------ *)

Notation sZ := Sint63.to_Z.

Lemma sZ_pos : forall d : int, (0 < sZ d)%Z -> to_Z d = sZ d.
Proof.
  intros d H. unfold Sint63.to_Z, Sint63Axioms.to_Z in *.
  destruct (d <? Sint63Axioms.min_int); [reflexivity |].
  pose proof (to_Z_bounded (0 - d)). lia.
Qed.

Lemma sZ_neg : forall d : int, (sZ d < 0)%Z -> to_Z (0 - d) = (- sZ d)%Z.
Proof.
  intros d H. unfold Sint63.to_Z, Sint63Axioms.to_Z in *.
  destruct (d <? Sint63Axioms.min_int); [pose proof (to_Z_bounded d); lia | lia].
Qed.

Lemma primes_ok : forall t, (t < 25)%nat -> to_Z primes.[of_Z (Z.of_nat t)] = pZ t.
Proof.
  intros t Ht. do 25 (destruct t as [| t]; [reflexivity |]). lia.
Qed.

Lemma sltb_iff : forall x y : int, Sint63.ltb x y = true <-> (sZ x < sZ y)%Z.
Proof.
  intros x y. rewrite Sint63Axioms.ltb_spec. rewrite Z.compare_lt_iff.
  reflexivity.
Qed.

Section LoopProof.
Context {St : Type}.

Lemma wloop_eq : forall (hi : int) cont (f : int -> St -> St) i s H,
  wloop hi cont f i s H =
  match bdec (i <? hi) with
  | left Hi =>
      if cont i s then wloop hi cont f (i + 1) (f i s) (Acc_inv H (dec_step hi i Hi))
      else s
  | right _ => s
  end.
Proof. intros. destruct H; reflexivity. Qed.

Lemma loop_inv : forall (P : int -> St -> Prop) (hi lo : int) cont f s,
  (to_Z lo <= to_Z hi)%Z -> P lo s ->
  (forall j t, (to_Z lo <= to_Z j < to_Z hi)%Z -> P j t -> cont j t = true ->
     P (j + 1) (f j t)) ->
  exists j, (to_Z lo <= to_Z j <= to_Z hi)%Z /\ P j (loop hi cont f lo s) /\
    (to_Z j = to_Z hi \/ ((to_Z j < to_Z hi)%Z /\ cont j (loop hi cont f lo s) = false)).
Proof.
  intros P hi lo cont f s Hle Hp Hstep. unfold loop.
  assert (G : forall n i t (H : Acc (Zwf 0) (gap hi i)), gap hi i = n ->
     (to_Z lo <= to_Z i <= to_Z hi)%Z -> P i t ->
     exists j, (to_Z lo <= to_Z j <= to_Z hi)%Z /\ P j (wloop hi cont f i t H) /\
       (to_Z j = to_Z hi \/ ((to_Z j < to_Z hi)%Z /\ cont j (wloop hi cont f i t H) = false))).
  { intros n. induction n as [n IH] using (well_founded_induction (Zwf_well_founded 0)).
    intros i t H En Hi Pt. rewrite wloop_eq. destruct (bdec (i <? hi)) as [Hlt | Hge].
    - pose proof Hlt as Hlt'. rewrite Uint63.ltb_spec in Hlt'.
      destruct (cont i t) eqn:Ec.
      + apply (IH (gap hi (i + 1))).
        * rewrite <- En. apply dec_step; exact Hlt.
        * reflexivity.
        * pose proof (to_Z_bounded hi).
          assert (to_Z (i + 1) = (to_Z i + 1)%Z) by sia. lia.
        * apply Hstep; auto; lia.
      + exists i. split; [lia |]. split; [exact Pt | right; split; [lia | exact Ec]].
    - assert (~ (to_Z i < to_Z hi)%Z) by (rewrite <- Uint63.ltb_spec; congruence).
      exists i. split; [lia |]. split; [exact Pt | left; lia]. }
  apply (G _ lo s _ eq_refl); [lia | exact Hp].
Qed.

Lemma for_inv : forall (P : int -> St -> Prop) (hi lo : int) f s,
  (to_Z lo <= to_Z hi)%Z -> P lo s ->
  (forall j t, (to_Z lo <= to_Z j < to_Z hi)%Z -> P j t -> P (j + 1) (f j t)) ->
  P hi (loop hi (fun _ _ => true) f lo s).
Proof.
  intros P hi lo f s Hle Hp Hstep.
  destruct (loop_inv P hi lo (fun _ _ => true) f s Hle Hp) as (j & _ & Pj & [E | [_ E]]).
  - intros j t Hj Pt _. apply Hstep; auto.
  - apply to_Z_inj in E. subst j. exact Pj.
  - discriminate.
Qed.

End LoopProof.

Lemma zofi_rec_eq : forall i H, zofi_rec i H =
  match bdec (i =? 0) with
  | left _ => 0%Z
  | right Hn =>
      let r := zofi_rec (i / 2) (Acc_inv H (dec_half i Hn)) in
      let bit := if i mod 2 =? 0 then 0%Z else 1%Z in
      (2 * r + bit)%Z
  end.
Proof. intros. destruct H; reflexivity. Qed.

Lemma zofi_spec : forall i, zofi i = to_Z i.
Proof.
  assert (G : forall n i H, to_Z i = n -> zofi_rec i H = to_Z i).
  { intros n. induction n as [n IH] using (well_founded_induction (Zwf_well_founded 0)).
    intros i H En. rewrite zofi_rec_eq. destruct (bdec (i =? 0)) as [E | E].
    - apply Uint63.eqb_spec in E. subst i. reflexivity.
    - cbv zeta. rewrite (IH (to_Z (i / 2))); [| rewrite <- En; apply dec_half; exact E | reflexivity].
      pose proof (to_Z_bounded i).
      destruct (i mod 2 =? 0) eqn:Em.
      + apply Uint63.eqb_spec in Em. apply (f_equal to_Z) in Em. sia.
      + apply Uint63.eqb_false_spec in Em.
        assert (to_Z (i mod 2) <> 0%Z) by (intros E'; apply Em, to_Z_inj; exact E'). sia. }
  intros i. unfold zofi. apply (G _ i _ eq_refl).
Qed.

Definition fdv (dv : int -> int) (t : nat) : Z := sZ (dv (of_Z (Z.of_nat t))).

Lemma exact_gt_spec : forall dv, exact_gt dv = true <-> (1 < Vp (fdv dv))%R.
Proof.
  intros dv. unfold exact_gt.
  pose (Pp := fun (t : int) (s : bool * Z * Z) =>
    let '(nz, P, Q) := s in (0 < P)%Z /\ (0 < Q)%Z /\
      (IZR P / IZR Q)%R = prodR (Z.to_nat (to_Z t))
                            (fun t' => powerRZ (IZR (pZ t')) (fdv dv t')) /\
      (nz = false -> P = 1%Z /\ Q = 1%Z)).
  assert (Hl : Pp 25 (loop 25 (fun _ _ => true) (ex_step dv) 0 (false, 1%Z, 1%Z))).
  { apply for_inv.
    - cbv. discriminate.
    - simpl. repeat split; try lia. simpl. field.
    - intros j [[nz P] Q] Hj (HP & HQ & HV & Hz).
      change (to_Z 0) with 0%Z in Hj. change (to_Z 25) with 25%Z in Hj.
      assert (Ej : to_Z (j + 1) = (to_Z j + 1)%Z) by sia.
      assert (En : Z.to_nat (to_Z (j + 1)) = S (Z.to_nat (to_Z j))) by (rewrite Ej; lia).
      set (n := Z.to_nat (to_Z j)) in *.
      assert (Ejn : of_Z (Z.of_nat n) = j)
        by (apply to_Z_inj; rewrite of_Z_spec; unfold n; rewrite Z2Nat.id by lia;
            apply Z.mod_small; pose proof (to_Z_bounded j); lia).
      assert (Hp : zofi primes.[j] = pZ n)
        by (rewrite zofi_spec, <- Ejn; apply primes_ok; unfold n; lia).
      assert (Hpp : (0 < pZ n)%Z) by (pose proof (pZ_bound n ltac:(unfold n; lia)); lia).
      assert (Hd : sZ (dv j) = fdv dv n) by (unfold fdv; rewrite Ejn; reflexivity).
      unfold ex_step, Pp. rewrite En. simpl prodR. rewrite <- HV.
      destruct (Sint63.ltb 0 (dv j)) eqn:E1.
      + apply sltb_iff in E1. change (sZ 0) with 0%Z in E1.
        rewrite Hp, zofi_spec, sZ_pos by exact E1. rewrite Hd in *.
        split; [| split; [| split]].
        * apply Z.mul_pos_pos; [exact HP | apply Z.pow_pos_nonneg; lia].
        * exact HQ.
        * rewrite mult_IZR, IZR_pow_powerRZ by lia. field. apply not_0_IZR. lia.
        * intros F; discriminate F.
      + destruct (Sint63.ltb (dv j) 0) eqn:E2.
        * apply sltb_iff in E2. change (sZ 0) with 0%Z in E2.
          rewrite Hp, zofi_spec, sZ_neg by exact E2. rewrite Hd in *.
          split; [| split; [| split]].
          -- exact HP.
          -- apply Z.mul_pos_pos; [exact HQ | apply Z.pow_pos_nonneg; lia].
          -- rewrite mult_IZR, IZR_pow_powerRZ by lia.
             replace (fdv dv n) with (- - fdv dv n)%Z by lia. rewrite powerRZ_neg'.
             field. split; [apply not_0_IZR; lia |].
             apply Rgt_not_eq, powerRZ_lt, IZR_lt. lia.
          -- intros F; discriminate F.
        * rewrite <- Bool.not_true_iff_false, sltb_iff in E1, E2.
          change (sZ 0) with 0%Z in E1, E2.
          assert (fdv dv n = 0%Z) by lia. rewrite H. simpl powerRZ.
          split; [exact HP | split; [exact HQ | split; [ring | exact Hz]]]. }
  destruct (loop 25 (fun _ _ => true) (ex_step dv) 0 (false, 1%Z, 1%Z)) as [[nz P] Q].
  destruct Hl as (HP & HQ & HV & Hz). change (Z.to_nat (to_Z 25)) with 25%nat in HV.
  fold (Vp (fdv dv)) in HV. rewrite <- HV.
  assert (HQr : (0 < IZR Q)%R) by (apply IZR_lt; exact HQ).
  destruct nz.
  - rewrite Z.ltb_lt. split.
    + intros L. apply (Rmult_lt_reg_r (IZR Q)); [exact HQr |].
      unfold Rdiv. rewrite Rmult_assoc, Rinv_l, Rmult_1_l, Rmult_1_r by lra.
      apply IZR_lt. exact L.
    + intros L. apply lt_IZR.
      apply (Rmult_lt_compat_r (IZR Q)) in L; [| exact HQr].
      unfold Rdiv in L. rewrite Rmult_assoc, Rinv_l, Rmult_1_l, Rmult_1_r in L by lra.
      exact L.
  - destruct (Hz eq_refl) as [-> ->]. split; [discriminate |]. intros L. lra.
Qed.

(* ================================================================== *)
(* Part D: the float pairs and the certified comparison                *)
(* ================================================================== *)

Local Notation bp := (Raux.bpow Zaux.radix2).

Section Floats.
Local Open Scope R_scope.

Lemma IZR_pow2 : forall k, (0 <= k)%Z -> IZR (2 ^ k) = bp k.
Proof. intros k Hk. destruct k as [| p | p]; [reflexivity | reflexivity | lia]. Qed.

Lemma bp_pos : forall e, 0 < bp e.
Proof. intros e. apply Raux.bpow_gt_0. Qed.

Lemma bp_plus : forall e f, bp (e + f) = bp e * bp f.
Proof. intros e f. apply Raux.bpow_plus. Qed.

Lemma bp_1 : bp 1 = 2.
Proof. reflexivity. Qed.

Lemma eta_small : eta_max <= u / 32.
Proof.
  unfold eta_max. apply Rle_trans with (bp (-57)); [apply Raux.bpow_le; lia |].
  unfold u. replace (-52)%Z with (-57 + 5)%Z by reflexivity. rewrite bp_plus.
  change (bp 5) with 32. lra.
Qed.

Lemma rnd_rel : forall z, / 16 <= z -> (1 - u) * z <= rnd z <= (1 + u) * z.
Proof.
  intros z Hz. destruct (rnd_model z) as (eps & eta & He & Ht & _ & ->).
  pose proof eta_small. pose proof u_pos.
  apply Raux.Rabs_le_inv in He. apply Raux.Rabs_le_inv in Ht.
  assert (z * eps <= z * (u / 2)) by (apply Rmult_le_compat_l; lra).
  assert (z * (- (u / 2)) <= z * eps) by (apply Rmult_le_compat_l; lra).
  assert (u / 32 <= z * u / 2) by nra.
  nra.
Qed.

Lemma rnd_int : forall n : Z, (Z.abs n < 2 ^ 53)%Z -> rnd (IZR n) = IZR n.
Proof. exact rnd_IZR. Qed.

Lemma rnd_1 : rnd 1 = 1.
Proof. exact (rnd_IZR 1 eq_refl). Qed.
Lemma rnd_2 : rnd 2 = 2.
Proof. exact (rnd_IZR 2 eq_refl). Qed.
Lemma rnd_4 : rnd 4 = 4.
Proof. exact (rnd_IZR 4 eq_refl). Qed.

Lemma rnd_between : forall lo hi z, lo <= z <= hi -> rnd lo = lo -> rnd hi = hi ->
  lo <= rnd z <= hi.
Proof.
  intros lo hi z [H1 H2] E1 E2. split.
  - rewrite <- E1 at 1. apply rnd_le, H1.
  - rewrite <- E2. apply rnd_le, H2.
Qed.

Lemma repr_one : repr f_one 1.
Proof. exact (repr_of_uint63_exact 1 eq_refl). Qed.
Lemma repr_two : repr f_two 2.
Proof. exact (repr_of_uint63_exact 2 eq_refl). Qed.
Lemma repr_c0 : repr f_c0 1048576.
Proof. exact (repr_of_uint63_exact 1048576 eq_refl). Qed.
Lemma repr_c1 : repr f_c1 1048577.
Proof. exact (repr_of_uint63_exact 1048577 eq_refl). Qed.

Lemma no_ovf : forall z, Rabs z <= 1000000000000 -> Rabs (rnd z) < bp 1024.
Proof.
  intros z H. apply rnd_no_overflow_small.
  apply Rle_trans with 1000000000000; [exact H |].
  apply Rle_trans with (bp 40); [change (bp 40) with 1099511627776; lra |].
  apply Raux.bpow_le. lia.
Qed.

Lemma repr_mul_ok : forall (x y : float) xr yr, repr x xr -> repr y yr ->
  Rabs (xr * yr) <= 1000000000000 -> repr (x * y)%float (rnd (xr * yr)).
Proof. intros. apply repr_mul; auto. apply no_ovf; auto. Qed.

Lemma repr_div_ok : forall (x y : float) xr yr, repr x xr -> repr y yr -> yr <> 0 ->
  Rabs (xr / yr) <= 1000000000000 -> repr (x / y)%float (rnd (xr / yr)).
Proof. intros. apply repr_div; auto. apply no_ovf; auto. Qed.

(* -- relative error bookkeeping -- *)
Definition within (L U X A : R) : Prop := L * X <= A <= U * X.

Lemma within_mul : forall L1 U1 X1 A1 L2 U2 X2 A2,
  0 <= L1 -> 0 <= L2 -> 0 <= X1 -> 0 <= X2 ->
  within L1 U1 X1 A1 -> within L2 U2 X2 A2 ->
  within (L1 * L2) (U1 * U2) (X1 * X2) (A1 * A2).
Proof.
  intros L1 U1 X1 A1 L2 U2 X2 A2 HL1 HL2 HX1 HX2 [H1 H1'] [H2 H2'].
  split.
  - replace (L1 * L2 * (X1 * X2)) with ((L1 * X1) * (L2 * X2)) by ring.
    apply Rmult_le_compat; try apply Rmult_le_pos; auto.
  - replace (U1 * U2 * (X1 * X2)) with ((U1 * X1) * (U2 * X2)) by ring.
    apply Rmult_le_compat; auto.
    + apply Rle_trans with (L1 * X1); [apply Rmult_le_pos | ]; auto.
    + apply Rle_trans with (L2 * X2); [apply Rmult_le_pos | ]; auto.
Qed.

Lemma within_trans : forall L U X A L' U' B,
  0 <= L -> 0 <= L' -> 0 <= U' -> 0 <= X -> within L U X A -> within L' U' A B ->
  within (L' * L) (U' * U) X B.
Proof.
  intros L U X A L' U' B HL HL' HU' HX [H1 H2] [H3 H4].
  assert (0 <= A) by (apply Rle_trans with (L * X); [apply Rmult_le_pos |]; auto).
  split.
  - apply Rle_trans with (L' * A); [| exact H3]. rewrite Rmult_assoc.
    apply Rmult_le_compat_l; auto.
  - apply Rle_trans with (U' * A); [exact H4 |]. rewrite Rmult_assoc.
    apply Rmult_le_compat_l; auto.
Qed.

Lemma within_scale : forall L U X A s, 0 < s -> within L U X A -> within L U (X * s) (A * s).
Proof.
  intros L U X A s Hs [H1 H2]. split.
  - rewrite <- Rmult_assoc. apply Rmult_le_compat_r; lra.
  - rewrite <- Rmult_assoc. apply Rmult_le_compat_r; lra.
Qed.

Lemma within_weaken : forall L U L' U' X A, 0 <= X -> L' <= L -> U <= U' ->
  within L U X A -> within L' U' X A.
Proof.
  intros L U L' U' X A HX HL HU [H1 H2]. split.
  - apply Rle_trans with (L * X); [apply Rmult_le_compat_r |]; auto.
  - apply Rle_trans with (U * X); [| apply Rmult_le_compat_r]; auto.
Qed.

Lemma within_rnd : forall z, / 16 <= z -> within (1 - u) (1 + u) z (rnd z).
Proof. intros z Hz. apply rnd_rel, Hz. Qed.

Lemma within_refl : forall X, 0 <= X -> within (1 - u) (1 + u) X X.
Proof. intros X HX. pose proof u_pos. split; nra. Qed.

Lemma u_small : u < / 1000000.
Proof. rewrite u_val. lra. Qed.

Lemma pow_lo_pos : forall n, 0 <= (1 - u) ^ n.
Proof. intros n. apply pow_le. pose proof u_small. lra. Qed.

Lemma pow_lo_le1 : forall n m, (n <= m)%nat -> (1 - u) ^ m <= (1 - u) ^ n.
Proof.
  intros n m H. pose proof u_pos. pose proof u_small.
  replace m with (n + (m - n))%nat by lia. rewrite pow_add.
  pose proof (pow_lo_pos n).
  assert ((1 - u) ^ (m - n) <= 1).
  { apply Rle_trans with (1 ^ (m - n)); [apply pow_incr; lra | rewrite pow1; lra]. }
  nra.
Qed.

Lemma pow_hi_ge : forall n m, (n <= m)%nat -> (1 + u) ^ n <= (1 + u) ^ m.
Proof. intros n m H. pose proof u_pos. apply Rle_pow; [lra | exact H]. Qed.

Lemma bernoulli : forall n, 1 - INR n * u <= (1 - u) ^ n.
Proof.
  pose proof u_pos. pose proof u_small.
  induction n as [| n IH]; [simpl; lra |].
  rewrite S_INR. change ((1 - u) ^ S n) with ((1 - u) * (1 - u) ^ n).
  pose proof (pos_INR n). pose proof (pow_lo_pos n).
  assert (INR n * u * u >= 0) by (apply Rle_ge; repeat apply Rmult_le_pos; lra).
  nra.
Qed.

Lemma pow_prod_le1 : forall n, (1 + u) ^ n * (1 - u) ^ n <= 1.
Proof.
  intros n. rewrite <- Rpow_mult_distr. pose proof u_pos. pose proof u_small.
  apply Rle_trans with (1 ^ n); [apply pow_incr; split; nra | rewrite pow1; lra].
Qed.

Definition Lc : R := 1 - / 4294967296.

Lemma pow_lo_cap : forall n, (Z.of_nat n <= 1048576)%Z -> Lc <= (1 - u) ^ n.
Proof.
  intros n Hn. eapply Rle_trans; [| apply bernoulli].
  unfold Lc. apply IZR_le in Hn. rewrite <- INR_IZR_INZ in Hn. rewrite u_val.
  pose proof (pos_INR n).
  assert (INR n * / 4503599627370496 <= 1048576 * / 4503599627370496)
    by (apply Rmult_le_compat_r; lra).
  lra.
Qed.

End Floats.

Section Cells.
Local Open Scope R_scope.

Definition NN (n : int) : nat := Z.to_nat (to_Z n).

(* a cell's float pair: the mantissa is in [1, 2]; the count is at most
   the cap plus one; within the cap, the exponent is near the bias and the
   pair is within (1 -+ u)^n of the exact value X *)
Definition cellF (m : float) (e n : int) (X : R) : Prop :=
  exists mr, repr m mr /\ 1 <= mr <= 2 /\ (to_Z n <= 1048577)%Z /\
    ((to_Z n <= 1048576)%Z ->
       (1073741824 - 8 * to_Z n <= to_Z e <= 1073741824 + 8 * to_Z n)%Z /\
       within ((1 - u) ^ NN n) ((1 + u) ^ NN n) X (mr * bp (to_Z e - 1073741824))).

Lemma cellF_one : cellF f_one BIAS 0 1.
Proof.
  exists 1. split; [exact repr_one |]. split; [lra |]. split; [cbv; discriminate |].
  intros _. split; [cbv; split; discriminate |].
  change (to_Z BIAS - 1073741824)%Z with 0%Z. unfold NN. simpl. split; lra.
Qed.

Lemma comp_core : forall X1 X2 A1 A2 (k1 k2 q : nat) z, 0 <= X1 -> 0 <= X2 ->
  within ((1 - u) ^ k1) ((1 + u) ^ k1) X1 A1 ->
  within ((1 - u) ^ k2) ((1 + u) ^ k2) X2 A2 ->
  within ((1 - u) ^ q) ((1 + u) ^ q) (A1 * A2) z ->
  within ((1 - u) ^ (k1 + k2 + q)) ((1 + u) ^ (k1 + k2 + q)) (X1 * X2) z.
Proof.
  intros X1 X2 A1 A2 k1 k2 q z H1 H2 W1 W2 W3.
  pose proof (within_mul _ _ _ _ _ _ _ _ (pow_lo_pos k1) (pow_lo_pos k2) H1 H2 W1 W2) as W.
  pose proof u_pos.
  assert (Hq : 0 <= (1 + u) ^ q) by (apply pow_le; lra).
  pose proof (within_trans _ _ _ _ _ _ _ (Rmult_le_pos _ _ (pow_lo_pos k1) (pow_lo_pos k2))
               (pow_lo_pos q) Hq (Rmult_le_pos _ _ H1 H2) W W3) as W'.
  rewrite !pow_add. replace ((1 - u) ^ k1 * (1 - u) ^ k2 * (1 - u) ^ q)
    with ((1 - u) ^ q * ((1 - u) ^ k1 * (1 - u) ^ k2)) by ring.
  replace ((1 + u) ^ k1 * (1 + u) ^ k2 * (1 + u) ^ q)
    with ((1 + u) ^ q * ((1 + u) ^ k1 * (1 + u) ^ k2)) by ring.
  exact W'.
Qed.

Lemma within_pow_weaken : forall k k' X A, (k <= k')%nat -> 0 <= X ->
  within ((1 - u) ^ k) ((1 + u) ^ k) X A -> within ((1 - u) ^ k') ((1 + u) ^ k') X A.
Proof.
  intros k k' X A Hk HX W. eapply within_weaken; [exact HX | | | exact W].
  - apply pow_lo_le1, Hk.
  - apply pow_hi_ge, Hk.
Qed.

Lemma within_1 : forall X A, within (1 - u) (1 + u) X A -> within ((1 - u) ^ 1) ((1 + u) ^ 1) X A.
Proof. intros X A W. simpl. rewrite !Rmult_1_r. exact W. Qed.

Lemma within_2 : forall X A B, 0 <= X -> within (1 - u) (1 + u) X A -> within (1 - u) (1 + u) A B ->
  within ((1 - u) ^ 2) ((1 + u) ^ 2) X B.
Proof.
  intros X A B HX W1 W2. pose proof u_pos. pose proof u_small.
  assert (Ha : 0 <= 1 - u) by lra. assert (Hb : 0 <= 1 + u) by lra.
  pose proof (within_trans _ _ _ _ _ _ _ Ha Ha Hb HX W1 W2) as W.
  simpl. rewrite !Rmult_1_r. exact W.
Qed.

Lemma mulcell_ok : forall m1 e1 n1 X1 m2 e2 n2 X2, 0 <= X1 -> 0 <= X2 ->
  cellF m1 e1 n1 X1 -> cellF m2 e2 n2 X2 ->
  let '(m, e, n) := mulcell m1 e1 n1 m2 e2 n2 in cellF m e n (X1 * X2).
Proof.
  intros m1 e1 n1 X1 m2 e2 n2 X2 HX1 HX2 [mr1 (R1 & B1 & C1 & K1)] [mr2 (R2 & B2 & C2 & K2)].
  pose proof u_pos. pose proof u_small.
  unfold mulcell.
  assert (Rp : repr (m1 * m2)%float (rnd (mr1 * mr2)))
    by (apply repr_mul_ok; auto; rewrite Rabs_right; nra).
  set (pr := rnd (mr1 * mr2)) in *.
  assert (Bp : 1 <= pr <= 4).
  { split; [rewrite <- rnd_1 | rewrite <- rnd_4]; apply rnd_le; nra. }
  assert (Wp : within (1 - u) (1 + u) (mr1 * mr2) pr) by (apply within_rnd; nra).
  pose proof (to_Z_bounded n1). pose proof (to_Z_bounded n2).
  pose proof (to_Z_bounded e1). pose proof (to_Z_bounded e2).
  assert (Hn : to_Z (n1 + n2 + 2)%uint63 = (to_Z n1 + to_Z n2 + 2)%Z) by sia.
  set (n := (n1 + n2 + 2)%uint63) in *.
  assert (Cn : (to_Z (if cap <? n then cap + 1 else n)%uint63 <= 1048577)%Z /\
               ((to_Z (if cap <? n then cap + 1 else n)%uint63 <= 1048576)%Z ->
                  (if cap <? n then cap + 1 else n)%uint63 = n /\ (to_Z n <= 1048576)%Z)).
  { destruct (cap <? n) eqn:E.
    - rewrite Uint63.ltb_spec in E. change (to_Z cap) with 1048576%Z in E.
      change (to_Z (cap + 1)%uint63) with 1048577%Z. split; [lia | intros F; lia].
    - rewrite <- Bool.not_true_iff_false, Uint63.ltb_spec in E.
      change (to_Z cap) with 1048576%Z in E. split; [lia | auto]. }
  set (n' := (if cap <? n then cap + 1 else n)%uint63) in *.
  destruct Cn as [Cn1 Cn2].
  assert (Hcert : (to_Z n' <= 1048576)%Z ->
     n' = n /\ (to_Z n1 <= 1048576)%Z /\ (to_Z n2 <= 1048576)%Z /\
     NN n' = (NN n1 + NN n2 + 2)%nat).
  { intros Hc. destruct (Cn2 Hc) as [E1 E2]. rewrite E1.
    split; [reflexivity |]. split; [lia | split; [lia |]].
    unfold NN. rewrite Hn. rewrite !Z2Nat.inj_add by lia. reflexivity. }
  destruct (f_two <=? m1 * m2)%float eqn:Ef.
  - rewrite (repr_leb_iff _ _ _ _ repr_two Rp) in Ef.
    exists (rnd (pr / 2)). split.
    { apply (repr_div_ok _ _ pr 2 Rp repr_two); [lra | rewrite Rabs_right; lra]. }
    split; [apply rnd_between; [lra | exact rnd_1 | exact rnd_2] |].
    split; [exact Cn1 |].
    intros Hc. destruct (Hcert Hc) as (_ & Hc1 & Hc2 & HN).
    destruct (K1 Hc1) as [Ke1 W1]. destruct (K2 Hc2) as [Ke2 W2].
    assert (He : to_Z (e1 + e2 - BIAS + 1)%uint63 = (to_Z e1 + to_Z e2 - 1073741824 + 1)%Z).
    { unfold BIAS. sia. }
    rewrite He. split; [lia |]. rewrite HN.
    apply (comp_core X1 X2 (mr1 * bp (to_Z e1 - 1073741824)) (mr2 * bp (to_Z e2 - 1073741824)));
      auto.
    replace (to_Z e1 + to_Z e2 - 1073741824 + 1 - 1073741824)%Z
      with ((to_Z e1 - 1073741824) + (to_Z e2 - 1073741824) + 1)%Z by ring.
    rewrite !bp_plus, bp_1.
    replace (mr1 * bp (to_Z e1 - 1073741824) * (mr2 * bp (to_Z e2 - 1073741824)))
      with (mr1 * mr2 * (bp (to_Z e1 - 1073741824) * bp (to_Z e2 - 1073741824))) by ring.
    replace (rnd (pr / 2) * (bp (to_Z e1 - 1073741824) * bp (to_Z e2 - 1073741824) * 2))
      with (rnd (pr / 2) * 2 * (bp (to_Z e1 - 1073741824) * bp (to_Z e2 - 1073741824))) by ring.
    apply within_scale; [apply Rmult_lt_0_compat; apply bp_pos |].
    apply (within_2 _ pr); [nra | exact Wp |].
    replace pr with (pr / 2 * 2) at 1 by field.
    apply within_scale; [lra |]. apply within_rnd. lra.
  - rewrite <- Bool.not_true_iff_false, (repr_leb_iff _ _ _ _ repr_two Rp) in Ef.
    exists pr. split; [exact Rp |]. split; [lra |]. split; [exact Cn1 |].
    intros Hc. destruct (Hcert Hc) as (_ & Hc1 & Hc2 & HN).
    destruct (K1 Hc1) as [Ke1 W1]. destruct (K2 Hc2) as [Ke2 W2].
    assert (He : to_Z (e1 + e2 - BIAS)%uint63 = (to_Z e1 + to_Z e2 - 1073741824)%Z).
    { unfold BIAS. sia. }
    rewrite He. split; [lia |]. rewrite HN.
    apply (within_pow_weaken (NN n1 + NN n2 + 1)); [lia | nra |].
    apply (comp_core X1 X2 (mr1 * bp (to_Z e1 - 1073741824)) (mr2 * bp (to_Z e2 - 1073741824)));
      auto.
    replace (to_Z e1 + to_Z e2 - 1073741824 - 1073741824)%Z
      with ((to_Z e1 - 1073741824) + (to_Z e2 - 1073741824))%Z by ring.
    rewrite !bp_plus.
    replace (mr1 * bp (to_Z e1 - 1073741824) * (mr2 * bp (to_Z e2 - 1073741824)))
      with (mr1 * mr2 * (bp (to_Z e1 - 1073741824) * bp (to_Z e2 - 1073741824))) by ring.
    apply within_scale; [apply Rmult_lt_0_compat; apply bp_pos |].
    apply within_1. exact Wp.
Qed.


Lemma ratecell_tail : forall (num den e : int) (E : Z) X,
  (1 <= to_Z num <= 6400)%Z -> (1 <= to_Z den <= 6400)%Z ->
  (to_Z den < 2 * to_Z num)%Z -> (to_Z num < 2 * to_Z den)%Z ->
  (-7 <= E <= 7)%Z -> to_Z e = (1073741824 + E)%Z ->
  X = IZR (to_Z num) / IZR (to_Z den) * bp E ->
  let r := (of_uint63 num / of_uint63 den)%float in
  let '(m, e', n) := if (r <? f_one)%float then ((r * f_two)%float, (e - 1)%uint63, 2%uint63)
                     else (r, e, 2%uint63) in
  cellF m e' n X.
Proof.
  intros num den e E X Hn Hd Hdn Hnd HE He HX r.
  pose proof u_pos. pose proof u_small.
  assert (Rn : repr (of_uint63 num) (IZR (to_Z num))) by (apply repr_of_uint63_exact; lia).
  assert (Rd : repr (of_uint63 den) (IZR (to_Z den))) by (apply repr_of_uint63_exact; lia).
  set (q := IZR (to_Z num) / IZR (to_Z den)) in *.
  assert (Dp : 1 <= IZR (to_Z den) <= 6400) by (split; apply IZR_le; lia).
  assert (Np : 1 <= IZR (to_Z num) <= 6400) by (split; apply IZR_le; lia).
  assert (Eq : q * IZR (to_Z den) = IZR (to_Z num)) by (unfold q; field; lra).
  assert (Q1 : IZR (to_Z den) + 1 <= 2 * IZR (to_Z num))
    by (rewrite <- (plus_IZR _ 1), <- (mult_IZR 2); apply IZR_le; lia).
  assert (Q2 : IZR (to_Z num) + 1 <= 2 * IZR (to_Z den))
    by (rewrite <- (plus_IZR _ 1), <- (mult_IZR 2); apply IZR_le; lia).
  assert (Bq : / 2 + / 12800 <= q <= 2) by nra.
  assert (Rr : repr r (rnd q)) by (apply (repr_div_ok _ _ _ _ Rn Rd); [lra | fold q; rewrite Rabs_right; lra]).
  set (rr := rnd q) in *.
  assert (Wr : within (1 - u) (1 + u) q rr) by (apply within_rnd; lra).
  assert (Br : / 2 < rr <= 2).
  { destruct Wr as [W1 W2]. split; [nra |].
    rewrite <- rnd_2. apply rnd_le. lra. }
  assert (Bp : 0 < bp E) by apply bp_pos.
  pose proof (to_Z_bounded e).
  destruct (r <? f_one)%float eqn:Ef.
  - rewrite (repr_ltb_iff _ _ _ _ Rr repr_one) in Ef.
    assert (Rm : repr (r * f_two)%float (rnd (rr * 2)))
      by (apply repr_mul_ok; auto; [exact repr_two | rewrite Rabs_right; lra]).
    exists (rnd (rr * 2)). split; [exact Rm |].
    split; [apply rnd_between; [lra | exact rnd_1 | exact rnd_2] |].
    split; [change (to_Z 2%uint63) with 2%Z; lia |]. intros _.
    assert (He1 : to_Z (e - 1)%uint63 = (1073741824 + E - 1)%Z) by sia.
    rewrite He1. change (to_Z 2%uint63) with 2%Z. split; [lia |].
    change (NN 2) with 2%nat.
    replace (1073741824 + E - 1 - 1073741824)%Z with (E + -1)%Z by ring.
    rewrite bp_plus. change (bp (-1)) with (/ 2).
    replace (rnd (rr * 2) * (bp E * / 2)) with (rnd (rr * 2) * / 2 * bp E) by ring.
    rewrite HX. apply within_scale; [exact Bp |].
    apply (within_2 _ rr); [lra | exact Wr |].
    replace rr with (rr * 2 * / 2) at 1 by field.
    apply within_scale; [lra |]. apply within_rnd. lra.
  - rewrite <- Bool.not_true_iff_false, (repr_ltb_iff _ _ _ _ Rr repr_one) in Ef.
    exists rr. split; [exact Rr |]. split; [lra |].
    split; [change (to_Z 2%uint63) with 2%Z; lia |]. intros _.
    rewrite He. change (to_Z 2%uint63) with 2%Z. split; [lia |].
    change (NN 2) with 2%nat.
    replace (1073741824 + E - 1073741824)%Z with E by ring.
    rewrite HX. apply within_scale; [exact Bp |].
    apply (within_pow_weaken 1); [lia | lra |]. apply within_1. exact Wr.
Qed.

Lemma head0_bounds : forall x : int, (1 <= to_Z x <= 100)%Z ->
  (56 <= to_Z (head0 x) <= 62)%Z /\
  (4611686018427387904 <= 2 ^ to_Z (head0 x) * to_Z x < 9223372036854775808)%Z.
Proof.
  intros x Hx. pose proof (head0_spec x ltac:(lia)) as H.
  change (wB / 2)%Z with 4611686018427387904%Z in H.
  change wB with 9223372036854775808%Z in H.
  pose proof (to_Z_bounded (head0 x)).
  split; [| exact H]. split.
  - destruct (Z_le_gt_dec 56 (to_Z (head0 x))) as [L | L]; [exact L | exfalso].
    assert (2 ^ to_Z (head0 x) <= 2 ^ 55)%Z by (apply Z.pow_le_mono_r; lia).
    change (2 ^ 55)%Z with 36028797018963968%Z in H1. nia.
  - destruct (Z_le_gt_dec (to_Z (head0 x)) 62) as [L | L]; [exact L | exfalso].
    assert (2 ^ 63 <= 2 ^ to_Z (head0 x))%Z by (apply Z.pow_le_mono_r; lia).
    change (2 ^ 63)%Z with 9223372036854775808%Z in H1. nia.
Qed.

Lemma ratecell_ok : forall a b : int, (1 <= to_Z a <= 100)%Z -> (1 <= to_Z b <= 100)%Z ->
  let '(m, e, n) := ratecell a b in cellF m e n (IZR (to_Z b) / IZR (to_Z a)).
Proof.
  intros a b Ha Hb. unfold ratecell.
  destruct (head0_bounds a Ha) as [Ba Pa]. destruct (head0_bounds b Hb) as [Bb Pb].
  set (ha := head0 a) in *. set (hb := head0 b) in *.
  assert (He : to_Z (BIAS + ha - hb)%uint63 = (1073741824 + (to_Z ha - to_Z hb))%Z)
    by (unfold BIAS; sia).
  assert (Pa0 : (0 < 2 ^ to_Z ha)%Z) by (apply Z.pow_pos_nonneg; lia).
  assert (Pb0 : (0 < 2 ^ to_Z hb)%Z) by (apply Z.pow_pos_nonneg; lia).
  destruct (ha <? hb) eqn:Eh.
  - rewrite Uint63.ltb_spec in Eh.
    set (s := (to_Z hb - to_Z ha)%Z).
    assert (Hs : to_Z (hb - ha)%uint63 = s) by (unfold s; sia).
    assert (Ps : (2 ^ to_Z hb = 2 ^ to_Z ha * 2 ^ s)%Z)
      by (unfold s; rewrite <- Z.pow_add_r by lia; f_equal; lia).
    assert (Ps0 : (2 <= 2 ^ s <= 64)%Z).
    { split; [change 2%Z with (2 ^ 1)%Z at 1 | change 64%Z with (2 ^ 6)%Z];
        apply Z.pow_le_mono_r; unfold s; lia. }
    assert (Hn : to_Z (b << (hb - ha))%uint63 = (to_Z b * 2 ^ s)%Z).
    { rewrite lsl_spec, Hs. apply Z.mod_small. change wB with 9223372036854775808%Z. nia. }
    apply (ratecell_tail _ _ _ (to_Z ha - to_Z hb)); try rewrite Hn; try lia.
    + nia.
    + nia.
    + nia.
    + rewrite mult_IZR, IZR_pow2 by (unfold s; lia).
      replace (to_Z ha - to_Z hb)%Z with (- s)%Z by (unfold s; ring).
      assert (Hbp : bp s * bp (- s) = 1)
        by (rewrite <- bp_plus; replace (s + - s)%Z with 0%Z by ring; reflexivity).
      assert (0 < bp s) by apply bp_pos.
      assert (0 < IZR (to_Z a)) by (apply IZR_lt; lia).
      transitivity (IZR (to_Z b) * (bp s * bp (- s)) / IZR (to_Z a));
        [rewrite Hbp; field; lra | field; lra].
  - rewrite <- Bool.not_true_iff_false, Uint63.ltb_spec in Eh.
    set (s := (to_Z ha - to_Z hb)%Z).
    assert (Hs : to_Z (ha - hb)%uint63 = s) by (unfold s; sia).
    assert (Ps : (2 ^ to_Z ha = 2 ^ to_Z hb * 2 ^ s)%Z)
      by (unfold s; rewrite <- Z.pow_add_r by lia; f_equal; lia).
    assert (Ps0 : (1 <= 2 ^ s <= 64)%Z).
    { split; [change 1%Z with (2 ^ 0)%Z at 1 | change 64%Z with (2 ^ 6)%Z];
        apply Z.pow_le_mono_r; unfold s; lia. }
    assert (Hd : to_Z (a << (ha - hb))%uint63 = (to_Z a * 2 ^ s)%Z).
    { rewrite lsl_spec, Hs. apply Z.mod_small. change wB with 9223372036854775808%Z. nia. }
    apply (ratecell_tail _ _ _ (to_Z ha - to_Z hb)); try rewrite Hd; try lia.
    + nia.
    + nia.
    + nia.
    + rewrite mult_IZR, IZR_pow2 by (unfold s; lia). fold s.
      assert (0 < bp s) by apply bp_pos.
      assert (0 < IZR (to_Z a)) by (apply IZR_lt; lia).
      field. lra.
Qed.


Lemma cert_bounds : forall m e n X, 0 < X -> cellF m e n X -> (to_Z n <= 1048576)%Z ->
  exists mr, repr m mr /\ 1 <= mr <= 2 /\
    (1073741824 - 8388608 <= to_Z e <= 1073741824 + 8388608)%Z /\
    Lc * (mr * bp (to_Z e - 1073741824)) <= X /\ X * Lc <= mr * bp (to_Z e - 1073741824).
Proof.
  intros m e n X HX [mr (R & B & C & K)] Hn. destruct (K Hn) as [Ke [W1 W2]].
  exists mr. split; [exact R |]. split; [exact B |]. split; [lia |].
  set (A := mr * bp (to_Z e - 1073741824)) in *.
  assert (HL : Lc <= (1 - u) ^ NN n) by (apply pow_lo_cap; unfold NN; lia).
  pose proof (pow_prod_le1 (NN n)) as Hp. pose proof (pow_lo_pos (NN n)).
  assert (0 < Lc) by (unfold Lc; lra).
  split.
  - apply Rle_trans with (Lc * ((1 + u) ^ NN n * X)); [apply Rmult_le_compat_l; lra |].
    apply Rle_trans with ((1 - u) ^ NN n * ((1 + u) ^ NN n * X)).
    + apply Rmult_le_compat_r; [| exact HL].
      apply Rmult_le_pos; [apply pow_le; pose proof u_pos; lra | lra].
    + replace ((1 - u) ^ NN n * ((1 + u) ^ NN n * X)) with (((1 + u) ^ NN n * (1 - u) ^ NN n) * X)
        by ring. nra.
  - apply Rle_trans with ((1 - u) ^ NN n * X); [| exact W1]. nra.
Qed.

Lemma cmp_exp_core : forall X1 X2 A1 A2, 0 < X2 ->
  Lc * A1 <= X1 -> X2 * Lc <= A2 -> 2 * A2 <= A1 -> X2 < X1.
Proof. intros. unfold Lc in *. lra. Qed.

Lemma cmp_mant_core : forall X1 X2 A1 A2 xr yr xc yc al be T,
  0 < T -> 0 < X2 -> A1 = al * T -> A2 = be * T -> 0 <= al -> 0 <= be ->
  Lc * A1 <= X1 -> X2 * Lc <= A2 ->
  (1 - u) * al <= xr <= (1 + u) * al -> (1 - u) * be <= yr <= (1 + u) * be ->
  (1 - u) * (yr * 1048577) <= yc -> xc <= (1 + u) * (xr * 1048576) -> yc < xc -> X2 < X1.
Proof.
  intros X1 X2 A1 A2 xr yr xc yc al be T HT HX2 HA1 HA2 Hal Hbe L1 L2 [Hx1 Hx2] [Hy1 Hy2] Hyc Hxc Hlt.
  assert (K : (1 - u) * (1 - u) * 1048577 * be < (1 + u) * (1 + u) * 1048576 * al).
  { pose proof u_pos. pose proof u_small.
    assert ((1 - u) * ((1 - u) * be * 1048577) <= (1 - u) * (yr * 1048577))
      by (apply Rmult_le_compat_l; lra).
    assert ((1 + u) * (xr * 1048576) <= (1 + u) * ((1 + u) * al * 1048576))
      by (apply Rmult_le_compat_l; lra).
    lra. }
  assert (K' : (1 - u) * (1 - u) * 1048577 * A2 < (1 + u) * (1 + u) * 1048576 * A1).
  { rewrite HA1, HA2. rewrite <- !Rmult_assoc. apply Rmult_lt_compat_r; [exact HT | exact K]. }
  unfold Lc in *. rewrite u_val in K'. lra.
Qed.

Lemma fcmp_ok : forall m1 e1 n1 X1 m2 e2 n2 X2, 0 < X1 -> 0 < X2 ->
  cellF m1 e1 n1 X1 -> cellF m2 e2 n2 X2 ->
  (fcmp m1 e1 n1 m2 e2 n2 = Some true -> X2 < X1) /\
  (fcmp m1 e1 n1 m2 e2 n2 = Some false -> X1 < X2).
Proof.
  intros m1 e1 n1 X1 m2 e2 n2 X2 HX1 HX2 C1 C2. unfold fcmp.
  destruct ((cap <? n1) || (cap <? n2)) eqn:Ec; [split; discriminate |].
  apply Bool.orb_false_iff in Ec as [Ec1 Ec2].
  rewrite <- Bool.not_true_iff_false, Uint63.ltb_spec in Ec1, Ec2.
  change (to_Z cap) with 1048576%Z in Ec1, Ec2.
  destruct (cert_bounds _ _ _ _ HX1 C1 ltac:(lia)) as (mr1 & R1 & B1 & E1 & L1 & U1).
  destruct (cert_bounds _ _ _ _ HX2 C2 ltac:(lia)) as (mr2 & R2 & B2 & E2 & L2 & U2).
  set (a1 := (to_Z e1 - 1073741824)%Z) in *. set (a2 := (to_Z e2 - 1073741824)%Z) in *.
  pose proof (bp_pos a1). pose proof (bp_pos a2).
  pose proof u_pos. pose proof u_small.
  destruct (e2 + 2 <=? e1) eqn:F1.
  { rewrite Uint63.leb_spec in F1.
    assert (Ha : (a2 + 2 <= a1)%Z) by (unfold a1, a2; sia).
    split; [intros _ | discriminate].
    apply (cmp_exp_core X1 X2 (mr1 * bp a1) (mr2 * bp a2) HX2 L1 U2).
    assert (bp (a2 + 2) <= bp a1) by (apply Raux.bpow_le; exact Ha).
    rewrite bp_plus in H3. change (bp 2) with 4 in H3. nra. }
  destruct (e1 + 2 <=? e2) eqn:F2.
  { rewrite Uint63.leb_spec in F2.
    assert (Ha : (a1 + 2 <= a2)%Z) by (unfold a1, a2; sia).
    split; [discriminate | intros _].
    apply (cmp_exp_core X2 X1 (mr2 * bp a2) (mr1 * bp a1) HX1 L2 U1).
    assert (bp (a1 + 2) <= bp a2) by (apply Raux.bpow_le; exact Ha).
    rewrite bp_plus in H3. change (bp 2) with 4 in H3. nra. }
  rewrite <- Bool.not_true_iff_false, Uint63.leb_spec in F1, F2.
  assert (Hd : (a1 <= a2 + 1 /\ a2 <= a1 + 1)%Z) by (unfold a1, a2; sia).
  set (t := Z.min a1 a2).
  assert (Hx : exists xr al, repr (if e2 <? e1 then (m1 * f_two)%float else m1) xr /\
     mr1 * bp a1 = al * bp t /\ 1 <= al <= 4 /\ (1 - u) * al <= xr <= (1 + u) * al).
  { destruct (e2 <? e1) eqn:G.
    - rewrite Uint63.ltb_spec in G.
      assert (Ht : a1 = (t + 1)%Z) by (unfold t, a1, a2 in *; lia).
      exists (rnd (mr1 * 2)), (mr1 * 2). split.
      + apply repr_mul_ok; [exact R1 | exact repr_two | rewrite Rabs_right; lra].
      + split; [rewrite Ht, bp_plus, bp_1; ring |]. split; [lra |].
        apply within_rnd. lra.
    - rewrite <- Bool.not_true_iff_false, Uint63.ltb_spec in G.
      assert (Ht : a1 = t) by (unfold t, a1, a2 in *; lia).
      exists mr1, mr1. split; [exact R1 |]. split; [rewrite Ht; ring |].
      split; [lra |]. split; nra. }
  assert (Hy : exists yr be, repr (if e1 <? e2 then (m2 * f_two)%float else m2) yr /\
     mr2 * bp a2 = be * bp t /\ 1 <= be <= 4 /\ (1 - u) * be <= yr <= (1 + u) * be).
  { destruct (e1 <? e2) eqn:G.
    - rewrite Uint63.ltb_spec in G.
      assert (Ht : a2 = (t + 1)%Z) by (unfold t, a1, a2 in *; lia).
      exists (rnd (mr2 * 2)), (mr2 * 2). split.
      + apply repr_mul_ok; [exact R2 | exact repr_two | rewrite Rabs_right; lra].
      + split; [rewrite Ht, bp_plus, bp_1; ring |]. split; [lra |].
        apply within_rnd. lra.
    - rewrite <- Bool.not_true_iff_false, Uint63.ltb_spec in G.
      assert (Ht : a2 = t) by (unfold t, a1, a2 in *; lia).
      exists mr2, mr2. split; [exact R2 |]. split; [rewrite Ht; ring |].
      split; [lra |]. split; nra. }
  destruct Hx as (xr & al & Rx & Hal & Bal & Wx).
  destruct Hy as (yr & be & Ry & Hbe & Bbe & Wy).
  set (x := if e2 <? e1 then (m1 * f_two)%float else m1) in *.
  set (y := if e1 <? e2 then (m2 * f_two)%float else m2) in *.
  pose proof (bp_pos t).
  assert (Ryc : repr (y * f_c1)%float (rnd (yr * 1048577)))
    by (apply repr_mul_ok; [exact Ry | exact repr_c1 | rewrite Rabs_right; nra]).
  assert (Rxc : repr (x * f_c0)%float (rnd (xr * 1048576)))
    by (apply repr_mul_ok; [exact Rx | exact repr_c0 | rewrite Rabs_right; nra]).
  assert (Rxc' : repr (x * f_c1)%float (rnd (xr * 1048577)))
    by (apply repr_mul_ok; [exact Rx | exact repr_c1 | rewrite Rabs_right; nra]).
  assert (Ryc' : repr (y * f_c0)%float (rnd (yr * 1048576)))
    by (apply repr_mul_ok; [exact Ry | exact repr_c0 | rewrite Rabs_right; nra]).
  destruct (y * f_c1 <? x * f_c0)%float eqn:G1.
  { rewrite (repr_ltb_iff _ _ _ _ Ryc Rxc) in G1. split; [intros _ | discriminate].
    destruct (rnd_rel (yr * 1048577) ltac:(nra)) as [Ry1 _].
    destruct (rnd_rel (xr * 1048576) ltac:(nra)) as [_ Rx2].
    apply (cmp_mant_core X1 X2 (mr1 * bp a1) (mr2 * bp a2) xr yr
             (rnd (xr * 1048576)) (rnd (yr * 1048577)) al be (bp t)); auto; lra. }
  destruct (x * f_c1 <? y * f_c0)%float eqn:G2.
  { rewrite (repr_ltb_iff _ _ _ _ Rxc' Ryc') in G2. split; [discriminate | intros _].
    destruct (rnd_rel (xr * 1048577) ltac:(nra)) as [Rx1 _].
    destruct (rnd_rel (yr * 1048576) ltac:(nra)) as [_ Ry2].
    apply (cmp_mant_core X2 X1 (mr2 * bp a2) (mr1 * bp a1) yr xr
             (rnd (yr * 1048576)) (rnd (xr * 1048577)) be al (bp t)); auto; lra. }
  split; discriminate.
Qed.

(* the full oracle: the float pairs when they are certain, else exact *)
Lemma oracle_ok : forall m1 e1 n1 X1 m2 e2 n2 X2 (dv : int -> int),
  0 < X1 -> 0 < X2 -> cellF m1 e1 n1 X1 -> cellF m2 e2 n2 X2 ->
  Vp (fdv dv) = X1 / X2 ->
  ((match fcmp m1 e1 n1 m2 e2 n2 with Some g => g | None => exact_gt dv end) = true
   <-> X2 < X1).
Proof.
  intros m1 e1 n1 X1 m2 e2 n2 X2 dv H1 H2 C1 C2 HV.
  destruct (fcmp_ok _ _ _ _ _ _ _ _ H1 H2 C1 C2) as [T F].
  destruct (fcmp m1 e1 n1 m2 e2 n2) as [[|] |].
  - split; [intros _; apply T; reflexivity | reflexivity].
  - split; [discriminate | intros L]. pose proof (F eq_refl). lra.
  - rewrite exact_gt_spec, HV. split; intros L.
    + apply (Rmult_lt_compat_r X2) in L; [| exact H2].
      unfold Rdiv in L. rewrite Rmult_assoc, Rinv_l, Rmult_1_r, Rmult_1_l in L by lra. exact L.
    + apply (Rmult_lt_reg_r X2); [exact H2 |].
      unfold Rdiv. rewrite Rmult_assoc, Rinv_l, Rmult_1_r, Rmult_1_l by lra. exact L.
Qed.

End Cells.

(* ================================================================== *)
(* Part E: the machine state and the loops                             *)
(* ================================================================== *)

Section Main.
Variables (c : N) (src dst a b : list N).
Variables (xc : uint) (xs xd xa xb : array uint).
Hypothesis Hv : valid_input c src dst a b.
Hypothesis Hc : repr xc c.
Hypothesis Hs : repr xs src.
Hypothesis Hd : repr xd dst.
Hypothesis Ha : repr xa a.
Hypothesis Hb : repr xb b.

Local Notation walk := (walk src dst).
Local Notation wprod := (wprod a b).
Local Notation rt := (rt a b).
Local Notation inter := (inter dst).

Definition NR : Z := Z.of_nat (List.length src).
Definition CZ : Z := Z.of_N c.

Lemma CZ_bounds : (1 <= CZ <= 200)%Z.
Proof. pose proof (vi_c _ _ _ _ _ Hv). unfold CZ. lia. Qed.

Lemma xc_val : to_Z xc = CZ.
Proof.
  unfold repr, repr_uint in Hc. unfold CZ. rewrite <- Hc.
  pose proof (to_Z_bounded xc). lia.
Qed.

Lemma NR_bound : (NR <= 39800)%Z.
Proof.
  pose proof (vi_r _ _ _ _ _ Hv). pose proof (vi_c _ _ _ _ _ Hv).
  unfold NR. unfold len in H. nia.
Qed.

Lemma len_arr : forall (t : array uint) (l : list N), repr t l ->
  to_Z (PArray.length t) = Z.of_nat (List.length l).
Proof. intros t l [E _]. symmetry. exact E. Qed.

Lemma arr_get0 : forall (t : array uint) (l : list N), repr t l ->
  forall i : int, (to_Z i < Z.of_nat (List.length l))%Z ->
  to_Z t.[i] = Z.of_N (lget l (Z.to_N (to_Z i))).
Proof.
  intros t l [_ H] i Hi. pose proof (to_Z_bounded i).
  destruct (H (Z.to_nat (to_Z i)) ltac:(lia)) as (m & E & R).
  unfold repr, repr_uint in R. rewrite Z2Nat.id in R by lia. rewrite of_to_Z in R.
  unfold lget, Prelude.get. rewrite Z_N_nat. rewrite (nth_error_nth _ _ _ E).
  rewrite <- R. pose proof (to_Z_bounded t.[i]). lia.
Qed.

Lemma arr_get : forall (t : array@{Set} uint) (l : list N), repr t l ->
  forall i : int, (to_Z i < Z.of_nat (List.length l))%Z ->
  to_Z (@PArray.get@{Set} uint t i) = Z.of_N (lget l (Z.to_N (to_Z i))).
Proof. intros t l H i Hi. exact (arr_get0 t l H i Hi). Qed.

Lemma len_src : len src = Z.to_N NR.
Proof. unfold len, NR. lia. Qed.

Lemma lget_in : forall (l : list N) k, (k < len l)%N -> In (lget l k) l.
Proof. intros l k H. unfold lget, Prelude.get. apply nth_In. unfold len in H. lia. Qed.

Lemma src_lt : forall k, (k < len src)%N -> (lget src k < c)%N.
Proof.
  intros k H. pose proof (vi_src _ _ _ _ _ Hv) as F. rewrite Forall_forall in F.
  apply F, lget_in, H.
Qed.

Lemma dst_lt : forall k, (k < len src)%N -> (lget dst k < c)%N.
Proof.
  intros k H. pose proof (vi_dst _ _ _ _ _ Hv) as F. rewrite Forall_forall in F.
  apply F, lget_in. rewrite (vi_dst_len _ _ _ _ _ Hv). exact H.
Qed.

Lemma a_rng : forall k, (k < len src)%N -> (1 <= lget a k <= 100)%N.
Proof.
  intros k H. pose proof (vi_a _ _ _ _ _ Hv) as F. rewrite Forall_forall in F.
  apply F, lget_in. rewrite (vi_a_len _ _ _ _ _ Hv). exact H.
Qed.

Lemma b_rng : forall k, (k < len src)%N -> (1 <= lget b k <= 100)%N.
Proof.
  intros k H. pose proof (vi_b _ _ _ _ _ Hv) as F. rewrite Forall_forall in F.
  apply F, lget_in. rewrite (vi_b_len _ _ _ _ _ Hv). exact H.
Qed.

(* -- the exponent vector of a walk -- *)
Definition rv (k : N) (t : nat) : Z :=
  (mZ (Z.of_N (lget b k)) (pZ t) - mZ (Z.of_N (lget a k)) (pZ t))%Z.
Definition wvec (ks : list N) (t : nat) : Z :=
  fold_right (fun k acc => (rv k t + acc)%Z) 0%Z ks.

Lemma rt_pos : forall k, (k < len src)%N -> (0 < rt k)%R.
Proof.
  intros k H. unfold arbitrage_implem.rt.
  pose proof (a_rng k H). pose proof (b_rng k H).
  apply Rdiv_lt_0_compat; apply IZR_lt; lia.
Qed.

Lemma wprod_pos : forall ks, Forall (fun k => (k < len src)%N) ks -> (0 < wprod ks)%R.
Proof.
  induction ks as [| k ks IH]; intros F; simpl; [lra |].
  inversion F; subst. apply Rmult_lt_0_compat; [apply rt_pos; auto | apply IH; auto].
Qed.

Lemma Vp_rv : forall k, (k < len src)%N -> Vp (rv k) = rt k.
Proof.
  intros k H. unfold rv. rewrite Vp_sub.
  pose proof (a_rng k H). pose proof (b_rng k H).
  rewrite !Vp_mZ by lia. reflexivity.
Qed.

Lemma wvec_cons : forall k ks t, wvec (k :: ks) t = (rv k t + wvec ks t)%Z.
Proof. reflexivity. Qed.

Lemma wvec_app : forall l1 l2 t, wvec (l1 ++ l2) t = (wvec l1 t + wvec l2 t)%Z.
Proof. induction l1 as [| k l1 IH]; intros; simpl; [lia | unfold wvec in *; simpl; rewrite IH; lia]. Qed.

Lemma Vp_wvec : forall ks, Forall (fun k => (k < len src)%N) ks -> Vp (wvec ks) = wprod ks.
Proof.
  induction ks as [| k ks IH]; intros F.
  - unfold Vp, wvec. simpl. ring.
  - inversion F; subst. simpl wprod.
    rewrite (Vp_ext (wvec (k :: ks)) (fun t => rv k t + wvec ks t)%Z) by (intros; reflexivity).
    rewrite Vp_add, Vp_rv, IH by auto. reflexivity.
Qed.

Lemma rv_bound : forall k t, (Z.abs (rv k t) <= 6)%Z.
Proof. intros k t. unfold rv. pose proof (mZ_bound (Z.of_N (lget b k)) (pZ t)).
  pose proof (mZ_bound (Z.of_N (lget a k)) (pZ t)). lia. Qed.

Lemma wvec_bound : forall ks t, (Z.abs (wvec ks t) <= 6 * Z.of_nat (List.length ks))%Z.
Proof.
  induction ks as [| k ks IH]; intros t; simpl; [lia |].
  unfold wvec in *. simpl. pose proof (rv_bound k t). specialize (IH t). lia.
Qed.

(* -- simple walks are short -- *)
Lemma in_removelast : forall (l : list N) v, In v (removelast l) -> In v l.
Proof.
  intros l v H. destruct l as [| x l]; [destruct H |].
  rewrite (app_removelast_last 0%N (l := x :: l)) by discriminate.
  apply in_or_app. left. exact H.
Qed.

Lemma inter_lt : forall ks v, Forall (fun k => (k < len src)%N) ks -> In v (inter ks) -> (v < c)%N.
Proof.
  intros ks v F Hin. unfold arbitrage_implem.inter in Hin.
  apply in_removelast in Hin.
  unfold verts in Hin. apply in_map_iff in Hin as (k & <- & Hk).
  rewrite Forall_forall in F. apply dst_lt, F, Hk.
Qed.

Lemma simple_len : forall x y ks, walk x y ks -> simple dst x y ks ->
  (Z.of_nat (List.length ks) <= CZ + 1)%Z.
Proof.
  intros x y ks [_ F] [Nd _].
  assert (L : (List.length (inter ks) <= N.to_nat c)%nat).
  { replace (N.to_nat c) with (List.length (map N.of_nat (seq 0 (N.to_nat c))))
      by (rewrite length_map, length_seq; reflexivity).
    apply NoDup_incl_length; [exact Nd |].
    intros v Hin. pose proof (inter_lt ks v F Hin).
    apply in_map_iff. exists (N.to_nat v). split; [lia |]. apply in_seq. lia. }
  rewrite length_inter in L. unfold CZ. lia.
Qed.

(* -- array plumbing -- *)
Lemma ilen_set : forall (t : array int) i v, PArray.length t.[i <- v] = PArray.length t.
Proof. intros t i v. exact (length_set int t i v). Qed.
Lemma flen_set : forall (t : array float) i v, PArray.length t.[i <- v] = PArray.length t.
Proof. intros t i v. exact (length_set float t i v). Qed.
Lemma blen_set : forall (t : array bool) i v, PArray.length t.[i <- v] = PArray.length t.
Proof. intros t i v. exact (length_set bool t i v). Qed.
Lemma iget_same : forall (t : array int) i v, (i <? PArray.length t) = true -> t.[i <- v].[i] = v.
Proof. intros t i v H. exact (get_set_same int t i v H). Qed.
Lemma fget_same : forall (t : array float) i v, (i <? PArray.length t) = true -> t.[i <- v].[i] = v.
Proof. intros t i v H. exact (get_set_same float t i v H). Qed.
Lemma bget_same : forall (t : array bool) i v, (i <? PArray.length t) = true -> t.[i <- v].[i] = v.
Proof. intros t i v H. exact (get_set_same bool t i v H). Qed.
Lemma iget_other : forall (t : array int) i j v, i <> j -> t.[i <- v].[j] = t.[j].
Proof. intros t i j v H. exact (get_set_other int t i j v H). Qed.
Lemma fget_other : forall (t : array float) i j v, i <> j -> t.[i <- v].[j] = t.[j].
Proof. intros t i j v H. exact (get_set_other float t i j v H). Qed.
Lemma bget_other : forall (t : array bool) i j v, i <> j -> t.[i <- v].[j] = t.[j].
Proof. intros t i j v H. exact (get_set_other bool t i j v H). Qed.
Lemma len_bound : forall {A} (t : array A), (to_Z (PArray.length t) <= 4194303)%Z.
Proof. intros A t. pose proof (leb_length A t) as H. rewrite Uint63.leb_spec in H. exact H. Qed.

Lemma vadd_spec : forall (bd b1 b2 : int) (V : array int),
  (to_Z bd + 25 <= to_Z (PArray.length V))%Z ->
  (to_Z b1 + 25 <= to_Z (PArray.length V))%Z -> (to_Z b2 + 25 <= to_Z (PArray.length V))%Z ->
  (to_Z b1 + 25 <= to_Z bd \/ to_Z bd + 25 <= to_Z b1)%Z ->
  (to_Z b2 + 25 <= to_Z bd \/ to_Z bd + 25 <= to_Z b2)%Z ->
  PArray.length (vadd bd b1 b2 V) = PArray.length V /\
  (forall t : int, (to_Z t < 25)%Z -> (vadd bd b1 b2 V).[bd + t] = V.[b1 + t] + V.[b2 + t]) /\
  (forall i : int, (to_Z i < to_Z bd \/ to_Z bd + 25 <= to_Z i)%Z -> (vadd bd b1 b2 V).[i] = V.[i]).
Proof.
  intros bd b1 b2 V Hbd H1 H2 D1 D2. pose proof (len_bound V).
  pose proof (to_Z_bounded bd). pose proof (to_Z_bounded b1). pose proof (to_Z_bounded b2).
  unfold vadd.
  apply (for_inv (fun t W => PArray.length W = PArray.length V /\
    (forall t' : int, (to_Z t' < to_Z t)%Z -> W.[bd + t'] = V.[b1 + t'] + V.[b2 + t']) /\
    (forall i : int, (to_Z i < to_Z bd \/ to_Z bd + to_Z t <= to_Z i)%Z -> W.[i] = V.[i]))).
  - change (to_Z 0) with 0%Z. change (to_Z 25) with 25%Z. lia.
  - split; [reflexivity |]. split.
    + intros t' Ht'. change (to_Z 0) with 0%Z in Ht'. pose proof (to_Z_bounded t'). lia.
    + intros i _. reflexivity.
  - intros j W Hj (HL & HA & HO).
    change (to_Z 0) with 0%Z in Hj. change (to_Z 25) with 25%Z in Hj.
    assert (Ej : to_Z (j + 1) = (to_Z j + 1)%Z) by sia.
    assert (Edj : to_Z (bd + j) = (to_Z bd + to_Z j)%Z) by sia.
    assert (E1j : to_Z (b1 + j) = (to_Z b1 + to_Z j)%Z) by sia.
    assert (E2j : to_Z (b2 + j) = (to_Z b2 + to_Z j)%Z) by sia.
    rewrite HO by lia. rewrite (HO (b2 + j)) by lia.
    split; [rewrite ilen_set; exact HL |]. split.
    + intros t' Ht'. rewrite Ej in Ht'.
      destruct (Z.eq_dec (to_Z t') (to_Z j)) as [E | E].
      * apply to_Z_inj in E. subst t'. apply iget_same.
        rewrite Uint63.ltb_spec, HL. lia.
      * pose proof (to_Z_bounded t').
        rewrite iget_other by (intros F; apply (f_equal to_Z) in F; sia).
        apply HA. lia.
    + intros i Hi. rewrite Ej in Hi.
      rewrite iget_other by (intros F; apply (f_equal to_Z) in F; lia).
      apply HO. lia.
Qed.

Lemma vset_spec : forall (bd : int) (f : int -> int) (V : array int),
  (to_Z bd + 25 <= to_Z (PArray.length V))%Z ->
  PArray.length (loop 25 (fun _ _ => true) (fun t W => W.[bd + t <- f t]) 0 V) = PArray.length V /\
  (forall t : int, (to_Z t < 25)%Z ->
     (loop 25 (fun _ _ => true) (fun t W => W.[bd + t <- f t]) 0 V).[bd + t] = f t) /\
  (forall i : int, (to_Z i < to_Z bd \/ to_Z bd + 25 <= to_Z i)%Z ->
     (loop 25 (fun _ _ => true) (fun t W => W.[bd + t <- f t]) 0 V).[i] = V.[i]).
Proof.
  intros bd f V Hbd. pose proof (len_bound V). pose proof (to_Z_bounded bd).
  apply (for_inv (fun t W => PArray.length W = PArray.length V /\
    (forall t' : int, (to_Z t' < to_Z t)%Z -> W.[bd + t'] = f t') /\
    (forall i : int, (to_Z i < to_Z bd \/ to_Z bd + to_Z t <= to_Z i)%Z -> W.[i] = V.[i]))).
  - change (to_Z 0) with 0%Z. change (to_Z 25) with 25%Z. lia.
  - split; [reflexivity |]. split.
    + intros t' Ht'. change (to_Z 0) with 0%Z in Ht'. pose proof (to_Z_bounded t'). lia.
    + intros i _. reflexivity.
  - intros j W Hj (HL & HA & HO).
    change (to_Z 0) with 0%Z in Hj. change (to_Z 25) with 25%Z in Hj.
    assert (Ej : to_Z (j + 1) = (to_Z j + 1)%Z) by sia.
    assert (Edj : to_Z (bd + j) = (to_Z bd + to_Z j)%Z) by sia.
    split; [rewrite ilen_set; exact HL |]. split.
    + intros t' Ht'. rewrite Ej in Ht'.
      destruct (Z.eq_dec (to_Z t') (to_Z j)) as [E | E].
      * apply to_Z_inj in E. subst t'. apply iget_same.
        rewrite Uint63.ltb_spec, HL. lia.
      * pose proof (to_Z_bounded t').
        rewrite iget_other by (intros F; apply (f_equal to_Z) in F; sia).
        apply HA. lia.
    + intros i Hi. rewrite Ej in Hi.
      rewrite iget_other by (intros F; apply (f_equal to_Z) in F; lia).
      apply HO. lia.
Qed.

(* -- cell indices -- *)
Definition qi (x y : N) : int := of_Z (Z.of_N x * CZ + Z.of_N y).
Definition vi (x y : N) (t : nat) : int := of_Z (25 * (Z.of_N x * CZ + Z.of_N y) + Z.of_nat t).

Lemma qi_val : forall x y, (x < c)%N -> (y < c)%N -> to_Z (qi x y) = (Z.of_N x * CZ + Z.of_N y)%Z.
Proof.
  intros x y Hx Hy. unfold qi. rewrite of_Z_spec. apply Z.mod_small.
  pose proof CZ_bounds. unfold CZ in *. change wB with 9223372036854775808%Z. nia.
Qed.

Lemma vi_val : forall x y t, (x < c)%N -> (y < c)%N -> (t < 25)%nat ->
  to_Z (vi x y t) = (25 * (Z.of_N x * CZ + Z.of_N y) + Z.of_nat t)%Z.
Proof.
  intros x y t Hx Hy Ht. unfold vi. rewrite of_Z_spec. apply Z.mod_small.
  pose proof CZ_bounds. unfold CZ in *. change wB with 9223372036854775808%Z. nia.
Qed.

Lemma cell_lt : forall x y, (x < c)%N -> (y < c)%N -> (Z.of_N x * CZ + Z.of_N y < CZ * CZ)%Z.
Proof. intros x y Hx Hy. unfold CZ. nia. Qed.

Lemma cell_inj : forall x y x' y', (x < c)%N -> (y < c)%N -> (x' < c)%N -> (y' < c)%N ->
  (Z.of_N x * CZ + Z.of_N y = Z.of_N x' * CZ + Z.of_N y')%Z -> x = x' /\ y = y'.
Proof.
  intros x y x' y' Hx Hy Hx' Hy' E. unfold CZ in *.
  assert (x = x') by nia. subst. split; [reflexivity | lia].
Qed.

Lemma vblock_out : forall x y x' y' t, (x < c)%N -> (y < c)%N -> (x' < c)%N -> (y' < c)%N ->
  (t < 25)%nat -> ~ (x' = x /\ y' = y) ->
  (to_Z (vi x' y' t) < 25 * (Z.of_N x * CZ + Z.of_N y) \/
   25 * (Z.of_N x * CZ + Z.of_N y) + 25 <= to_Z (vi x' y' t))%Z.
Proof.
  intros x y x' y' t Hx Hy Hx' Hy' Ht N. rewrite vi_val by assumption.
  destruct (Z.lt_total (Z.of_N x' * CZ + Z.of_N y') (Z.of_N x * CZ + Z.of_N y)) as [L | [E | L]].
  - left. lia.
  - exfalso. apply N. apply cell_inj in E; [tauto | assumption ..].
  - right. lia.
Qed.

Definition Dset (D : N -> N -> option (list N)) (x y : N) (o : option (list N))
  : N -> N -> option (list N) :=
  fun x' y' => if N.eqb x' x && N.eqb y' y then o else D x' y'.

Definition isS (o : option (list N)) : bool := match o with Some _ => true | None => false end.

Definition Cell (T : tabs) (x y : N) (o : option (list N)) : Prop :=
  (tPR T).[qi x y] = isS o /\
  forall w, o = Some w ->
    cellF (tMA T).[qi x y] (tEX T).[qi x y] (tCN T).[qi x y] (wprod w) /\
    Forall (fun k => (k < len src)%N) w /\
    (Z.of_nat (List.length w) <= 2 * CZ + 2)%Z /\
    forall t, (t < 25)%nat -> sZ (tVT T).[vi x y t] = wvec w t.

Definition Rep (T : tabs) (D : N -> N -> option (list N)) : Prop :=
  to_Z (PArray.length (tPR T)) = (CZ * CZ)%Z /\
  to_Z (PArray.length (tMA T)) = (CZ * CZ)%Z /\
  to_Z (PArray.length (tEX T)) = (CZ * CZ)%Z /\
  to_Z (PArray.length (tCN T)) = (CZ * CZ)%Z /\
  to_Z (PArray.length (tVT T)) = (25 * (CZ * CZ))%Z /\
  forall x y, (x < c)%N -> (y < c)%N -> Cell T x y (D x y).

Lemma Rep_ext : forall T D D', (forall x y, (x < c)%N -> (y < c)%N -> D x y = D' x y) ->
  Rep T D -> Rep T D'.
Proof.
  intros T D D' E (L1 & L2 & L3 & L4 & L5 & HC). repeat (split; [assumption |]).
  intros x y Hx Hy. rewrite <- E by assumption. apply HC; assumption.
Qed.

Lemma Rep_write : forall T D x y w m e n V',
  Rep T D -> (x < c)%N -> (y < c)%N ->
  cellF m e n (wprod w) -> Forall (fun k => (k < len src)%N) w ->
  (Z.of_nat (List.length w) <= 2 * CZ + 2)%Z ->
  to_Z (PArray.length V') = (25 * (CZ * CZ))%Z ->
  (forall t, (t < 25)%nat -> sZ V'.[vi x y t] = wvec w t) ->
  (forall i : int, (to_Z i < 25 * (Z.of_N x * CZ + Z.of_N y) \/
                    25 * (Z.of_N x * CZ + Z.of_N y) + 25 <= to_Z i)%Z -> V'.[i] = (tVT T).[i]) ->
  Rep (wr_head T (qi x y) m e n V') (Dset D x y (Some w)).
Proof.
  intros T D x y w m e n V' (L1 & L2 & L3 & L4 & L5 & HC) Hx Hy Cm Fw Lw LV HV HO.
  pose proof (qi_val x y Hx Hy) as Q. pose proof (cell_lt x y Hx Hy) as Q'.
  unfold wr_head, Rep. simpl.
  split; [rewrite blen_set; exact L1 |].
  split; [rewrite flen_set; exact L2 |].
  split; [rewrite ilen_set; exact L3 |].
  split; [rewrite ilen_set; exact L4 |].
  split; [exact LV |].
  intros x' y' Hx' Hy'. unfold Dset.
  destruct (N.eqb_spec x' x) as [Ex | Ex]; destruct (N.eqb_spec y' y) as [Ey | Ey];
    unfold Cell; simpl.
  1: { subst x' y'. assert (Hq : (qi x y <? PArray.length (tPR T)) = true)
      by (rewrite Uint63.ltb_spec, Q, L1; exact Q').
    split; [apply bget_same; exact Hq |].
    intros w' Ew. injection Ew as <-.
    rewrite fget_same by (rewrite Uint63.ltb_spec, Q, L2; exact Q').
    rewrite (iget_same (tEX T)) by (rewrite Uint63.ltb_spec, Q, L3; exact Q').
    rewrite (iget_same (tCN T)) by (rewrite Uint63.ltb_spec, Q, L4; exact Q').
    split; [exact Cm |]. split; [exact Fw |]. split; [exact Lw |]. exact HV. }
    all: assert (Nxy : ~ (x' = x /\ y' = y)) by tauto.
    all: assert (Nq : qi x y <> qi x' y')
      by (intros F; apply (f_equal to_Z) in F; rewrite Q, qi_val in F by assumption;
          apply cell_inj in F; [destruct F as [F1 F2]; apply Nxy; split; congruence | assumption ..]).
    all: destruct (HC x' y' Hx' Hy') as [P1 P2].
    all: split; [rewrite bget_other by exact Nq; exact P1 |].
    all: intros w' Ew; destruct (P2 w' Ew) as (C1 & C2 & C3 & C4).
    all: rewrite fget_other, !iget_other by exact Nq.
    all: split; [exact C1 |]; split; [exact C2 |]; split; [exact C3 |].
    all: intros t Ht; rewrite HO; [apply C4; exact Ht |].
    all: apply vblock_out; assumption.
Qed.

Lemma ilen_make : forall n (v : int), PArray.length (PArray.make n v) =
  if n <=? max_length then n else max_length.
Proof. intros n v. exact (length_make int n v). Qed.
Lemma flen_make : forall n (v : float), PArray.length (PArray.make n v) =
  if n <=? max_length then n else max_length.
Proof. intros n v. exact (length_make float n v). Qed.
Lemma blen_make : forall n (v : bool), PArray.length (PArray.make n v) =
  if n <=? max_length then n else max_length.
Proof. intros n v. exact (length_make bool n v). Qed.
Lemma bget_make : forall n (v : bool) i, (PArray.make n v).[i] = v.
Proof. intros n v i. exact (get_make bool v n i). Qed.

(* -- small signed words -- *)
Lemma sZ_small : forall x : int, (to_Z x < 4611686018427387904)%Z -> sZ x = to_Z x.
Proof.
  intros x H. unfold Sint63.to_Z, Sint63Axioms.to_Z.
  replace (x <? Sint63Axioms.min_int) with true; [reflexivity |].
  symmetry. rewrite Uint63.ltb_spec. exact H.
Qed.

Lemma sZ_add : forall x y : int, (Z.abs (sZ x + sZ y) < 4611686018427387904)%Z ->
  sZ (x + y) = (sZ x + sZ y)%Z.
Proof.
  intros x y H. rewrite Sint63.add_spec. apply Sint63.cmod_small.
  change (wB / 2)%Z with 4611686018427387904%Z. lia.
Qed.

Lemma sZ_sub : forall x y : int, (Z.abs (sZ x - sZ y) < 4611686018427387904)%Z ->
  sZ (x - y) = (sZ x - sZ y)%Z.
Proof.
  intros x y H. rewrite Sint63.sub_spec. apply Sint63.cmod_small.
  change (wB / 2)%Z with 4611686018427387904%Z. lia.
Qed.

Lemma dvd1_ok : forall n x : int, (0 < to_Z x)%Z -> to_Z (dvd1 n x) = dvdZ (to_Z n) (to_Z x).
Proof.
  intros n x Hx. unfold dvd1, dvdZ. rewrite <- Uint63.mod_spec.
  destruct (n mod x =? 0) eqn:E.
  - apply Uint63.eqb_spec in E. rewrite E. reflexivity.
  - apply Uint63.eqb_false_spec in E.
    destruct (Z.eqb_spec (to_Z (n mod x)) 0) as [F | F]; [| reflexivity].
    exfalso. apply E, to_Z_inj. exact F.
Qed.

Lemma mlt_ok : forall (n : int) t, (1 <= to_Z n <= 100)%Z -> (t < 25)%nat ->
  to_Z (mlt n primes.[of_Z (Z.of_nat t)]) = mZ (to_Z n) (pZ t).
Proof.
  intros n t Hn Ht. pose proof (primes_ok t Ht) as Hp. pose proof (pZ_bound t Ht) as Bp.
  set (p := primes.[of_Z (Z.of_nat t)]) in *. unfold mlt, mZ.
  assert (E2 : to_Z (p * p) = (pZ t ^ 2)%Z).
  { rewrite Uint63.mul_spec, Hp, Z.pow_2_r. apply Z.mod_small. change wB with 9223372036854775808%Z. nia. }
  assert (E3 : to_Z (p * p * p) = (pZ t ^ 3)%Z).
  { rewrite Uint63.mul_spec, E2, Hp. replace (pZ t ^ 2 * pZ t)%Z with (pZ t ^ 3)%Z by ring.
    apply Z.mod_small.
    change wB with 9223372036854775808%Z. split; [apply Z.pow_nonneg; lia |].
    apply Z.le_lt_trans with (97 ^ 3)%Z; [apply Z.pow_le_mono_l; lia | reflexivity]. }
  assert (E4 : to_Z (p * p * p * p) = (pZ t ^ 4)%Z).
  { rewrite Uint63.mul_spec, E3, Hp. replace (pZ t ^ 3 * pZ t)%Z with (pZ t ^ 4)%Z by ring.
    apply Z.mod_small.
    change wB with 9223372036854775808%Z. split; [apply Z.pow_nonneg; lia |].
    apply Z.le_lt_trans with (97 ^ 4)%Z; [apply Z.pow_le_mono_l; lia | reflexivity]. }
  assert (E5 : to_Z (p * p * p * p * p) = (pZ t ^ 5)%Z).
  { rewrite Uint63.mul_spec, E4, Hp. replace (pZ t ^ 4 * pZ t)%Z with (pZ t ^ 5)%Z by ring.
    apply Z.mod_small.
    change wB with 9223372036854775808%Z. split; [apply Z.pow_nonneg; lia |].
    apply Z.le_lt_trans with (97 ^ 5)%Z; [apply Z.pow_le_mono_l; lia | reflexivity]. }
  assert (E6 : to_Z (p * p * p * p * p * p) = (pZ t ^ 6)%Z).
  { rewrite Uint63.mul_spec, E5, Hp. replace (pZ t ^ 5 * pZ t)%Z with (pZ t ^ 6)%Z by ring.
    apply Z.mod_small.
    change wB with 9223372036854775808%Z. split; [apply Z.pow_nonneg; lia |].
    apply Z.le_lt_trans with (97 ^ 6)%Z; [apply Z.pow_le_mono_l; lia | reflexivity]. }
  assert (P2 : (0 < pZ t ^ 2)%Z) by (apply Z.pow_pos_nonneg; lia).
  assert (P3 : (0 < pZ t ^ 3)%Z) by (apply Z.pow_pos_nonneg; lia).
  assert (P4 : (0 < pZ t ^ 4)%Z) by (apply Z.pow_pos_nonneg; lia).
  assert (P5 : (0 < pZ t ^ 5)%Z) by (apply Z.pow_pos_nonneg; lia).
  assert (P6 : (0 < pZ t ^ 6)%Z) by (apply Z.pow_pos_nonneg; lia).
  cbv zeta.
  pose proof (dvd1_ok n p ltac:(lia)) as D1.
  pose proof (dvd1_ok n (p * p) ltac:(lia)) as D2.
  pose proof (dvd1_ok n (p * p * p) ltac:(lia)) as D3.
  pose proof (dvd1_ok n (p * p * p * p) ltac:(lia)) as D4.
  pose proof (dvd1_ok n (p * p * p * p * p) ltac:(lia)) as D5.
  pose proof (dvd1_ok n (p * p * p * p * p * p) ltac:(lia)) as D6.
  rewrite Hp, E2 in *. rewrite E3 in D3. rewrite E4 in D4. rewrite E5 in D5. rewrite E6 in D6.
  assert (B : forall z w, (0 <= dvdZ z w <= 1)%Z)
    by (intros z w; unfold dvdZ; destruct (Z.eqb _ _); lia).
  pose proof (B (to_Z n) (pZ t)). pose proof (B (to_Z n) (pZ t ^ 2)%Z).
  pose proof (B (to_Z n) (pZ t ^ 3)%Z). pose proof (B (to_Z n) (pZ t ^ 4)%Z).
  pose proof (B (to_Z n) (pZ t ^ 5)%Z). pose proof (B (to_Z n) (pZ t ^ 6)%Z).
  rewrite !Uint63.add_spec. rewrite D1, D2, D3, D4, D5, D6.
  rewrite !(Z.mod_small _ wB); change wB with 9223372036854775808%Z; lia.
Qed.

(* -- machine indices -- *)
Lemma t25_val : forall t, (t < 25)%nat -> to_Z (of_Z (Z.of_nat t)) = Z.of_nat t.
Proof. intros t Ht. rewrite of_Z_spec. apply Z.mod_small. change wB with 9223372036854775808%Z. lia. Qed.

Lemma t25_lt : forall t, (t < 25)%nat -> (to_Z (of_Z (Z.of_nat t)) < 25)%Z.
Proof. intros t Ht. rewrite t25_val by exact Ht. lia. Qed.

Lemma idx_q : forall (i j : int) (x y : N), to_Z i = Z.of_N x -> to_Z j = Z.of_N y ->
  (x < c)%N -> (y < c)%N -> i * xc + j = qi x y.
Proof.
  intros i j x y Ei Ej Hx Hy. apply to_Z_inj. rewrite qi_val by assumption.
  rewrite Uint63.add_spec, Uint63.mul_spec, Ei, Ej, xc_val.
  pose proof CZ_bounds. change wB with 9223372036854775808%Z.
  rewrite (Z.mod_small (Z.of_N x * CZ)) by (unfold CZ in *; nia).
  apply Z.mod_small. unfold CZ in *. nia.
Qed.

Lemma idx_v : forall (x y : N) t, (x < c)%N -> (y < c)%N -> (t < 25)%nat ->
  25 * qi x y + of_Z (Z.of_nat t) = vi x y t.
Proof.
  intros x y t Hx Hy Ht. apply to_Z_inj. rewrite vi_val by assumption.
  rewrite Uint63.add_spec, Uint63.mul_spec, qi_val by assumption.
  rewrite of_Z_spec. pose proof (cell_lt x y Hx Hy). pose proof CZ_bounds.
  change wB with 9223372036854775808%Z. change (to_Z 25) with 25%Z.
  rewrite (Z.mod_small (Z.of_nat t)) by lia.
  rewrite (Z.mod_small (25 * _)) by (unfold CZ in *; nia).
  apply Z.mod_small. unfold CZ in *. nia.
Qed.

Lemma qi_lt : forall x y, (x < c)%N -> (y < c)%N -> (to_Z (qi x y) < CZ * CZ)%Z.
Proof. intros x y Hx Hy. rewrite qi_val by assumption. apply cell_lt; assumption. Qed.

Lemma bd_val : forall x y, (x < c)%N -> (y < c)%N ->
  to_Z (25 * qi x y) = (25 * (Z.of_N x * CZ + Z.of_N y))%Z.
Proof.
  intros x y Hx Hy. rewrite Uint63.mul_spec, qi_val by assumption.
  pose proof (cell_lt x y Hx Hy). pose proof CZ_bounds. change (to_Z 25) with 25%Z.
  apply Z.mod_small. change wB with 9223372036854775808%Z. unfold CZ in *. nia.
Qed.

Lemma len_dst : Z.of_nat (List.length dst) = NR.
Proof. pose proof (vi_dst_len _ _ _ _ _ Hv). unfold len, NR in *. lia. Qed.
Lemma len_a : Z.of_nat (List.length a) = NR.
Proof. pose proof (vi_a_len _ _ _ _ _ Hv). unfold len, NR in *. lia. Qed.
Lemma len_b : Z.of_nat (List.length b) = NR.
Proof. pose proof (vi_b_len _ _ _ _ _ Hv). unfold len, NR in *. lia. Qed.

(* the vector of the rate b_k / a_k, as the machine computes it *)
Lemma sZ_rate : forall (r : int) t, (to_Z r < NR)%Z -> (t < 25)%nat ->
  sZ (mlt xb.[r] primes.[of_Z (Z.of_nat t)] - mlt xa.[r] primes.[of_Z (Z.of_nat t)])
  = rv (Z.to_N (to_Z r)) t.
Proof.
  intros r t Hr Ht. pose proof (to_Z_bounded r).
  set (k := Z.to_N (to_Z r)).
  assert (Hk : (k < len src)%N) by (unfold k; rewrite len_src; lia).
  pose proof (a_rng k Hk). pose proof (b_rng k Hk).
  assert (Ea : to_Z xa.[r] = Z.of_N (lget a k)) by (apply arr_get; [exact Ha | rewrite len_a; lia]).
  assert (Eb : to_Z xb.[r] = Z.of_N (lget b k)) by (apply arr_get; [exact Hb | rewrite len_b; lia]).
  pose proof (mlt_ok xa.[r] t ltac:(lia) Ht) as Ma. pose proof (mlt_ok xb.[r] t ltac:(lia) Ht) as Mb.
  rewrite Ea in Ma. rewrite Eb in Mb.
  pose proof (mZ_bound (Z.of_N (lget a k)) (pZ t)). pose proof (mZ_bound (Z.of_N (lget b k)) (pZ t)).
  assert (Sa : sZ (mlt xa.[r] primes.[of_Z (Z.of_nat t)]) = mZ (Z.of_N (lget a k)) (pZ t))
    by (rewrite sZ_small; lia).
  assert (Sb : sZ (mlt xb.[r] primes.[of_Z (Z.of_nat t)]) = mZ (Z.of_N (lget b k)) (pZ t))
    by (rewrite sZ_small; lia).
  rewrite sZ_sub; rewrite Sa, Sb; [unfold rv; reflexivity | lia].
Qed.

Definition InitInv (r : N) (D : N -> N -> option (list N)) : Prop :=
  (forall x y w, D x y = Some w ->
     exists k, w = [k] /\ (k < r)%N /\ lget src k = x /\ lget dst k = y) /\
  (forall k, (k < r)%N ->
     exists w, D (lget src k) (lget dst k) = Some w /\ (rt k <= wprod w)%R).

Lemma small2 : forall z1 z2 : Z, (Z.abs z1 <= 100000)%Z -> (Z.abs z2 <= 100000)%Z ->
  (Z.abs (z1 - z2) < 4611686018427387904)%Z.
Proof. intros. lia. Qed.

Lemma small2p : forall z1 z2 : Z, (Z.abs z1 <= 100000)%Z -> (Z.abs z2 <= 100000)%Z ->
  (Z.abs (z1 + z2) < 4611686018427387904)%Z.
Proof. intros. lia. Qed.

Lemma rv_small : forall k t, (Z.abs (rv k t) <= 100000)%Z.
Proof. intros k t. pose proof (rv_bound k t). lia. Qed.

Lemma wvec_small : forall w t, (Z.of_nat (List.length w) <= 2 * CZ + 2)%Z ->
  (Z.abs (wvec w t) <= 100000)%Z.
Proof. intros w t H. pose proof (wvec_bound w t). pose proof CZ_bounds. lia. Qed.

Lemma initinv_step : forall D k (bt : bool), (k < len src)%N ->
  InitInv k D ->
  (bt = true <-> match D (lget src k) (lget dst k) with
                 | None => True | Some w => (wprod w < rt k)%R end) ->
  InitInv (k + 1) (if bt then Dset D (lget src k) (lget dst k) (Some [k]) else D).
Proof.
  intros D k bt Hk [I1 I2] Hbt. split.
  - intros x' y' w' E. destruct bt.
    + unfold Dset in E.
      destruct (N.eqb_spec x' (lget src k)), (N.eqb_spec y' (lget dst k)); simpl in E.
      1: { injection E as <-. exists k. split; [reflexivity |]. split; [lia | auto]. }
      all: destruct (I1 _ _ _ E) as (k' & -> & Hk' & S1 & S2);
          exists k'; split; [reflexivity | split; [lia | auto]].
    + destruct (I1 _ _ _ E) as (k' & -> & Hk' & S1 & S2);
        exists k'; split; [reflexivity | split; [lia | auto]].
  - intros k' Hk'.
    assert (Hkk : k' = k \/ (k' < k)%N) by lia.
    destruct bt.
    + unfold Dset.
      destruct (N.eqb_spec (lget src k') (lget src k)), (N.eqb_spec (lget dst k') (lget dst k));
        simpl.
      1: { destruct Hkk as [-> | Hkk].
        - exists [k]. split; [reflexivity | simpl; lra].
        - exists [k]. split; [reflexivity |].
          destruct (I2 k' Hkk) as (w & Ew & Lw). rewrite e, e0 in Ew.
          rewrite Ew in Hbt. destruct Hbt as [Hbt _]. specialize (Hbt eq_refl).
          simpl. lra. }
      all: destruct Hkk as [-> | Hkk]; [congruence | apply I2; exact Hkk].
    + destruct Hkk as [-> | Hkk]; [| apply I2; exact Hkk].
      destruct (D (lget src k) (lget dst k)) as [w |] eqn:Ew.
      * exists w. split; [reflexivity |].
        destruct (Rlt_dec (wprod w) (rt k)) as [L | L]; [| lra].
        apply Hbt in L. discriminate.
      * destruct Hbt as [_ Hbt]. specialize (Hbt I). discriminate.
Qed.

Lemma init_step_ok : forall (r : int) T D, (to_Z r < NR)%Z -> Rep T D ->
  InitInv (Z.to_N (to_Z r)) D ->
  exists D', Rep (init_step xc xs xd xa xb r T) D' /\ InitInv (Z.to_N (to_Z r) + 1) D'.
Proof.
  intros r T D Hr HR [I1 I2].
  pose proof (to_Z_bounded r) as Br.
  set (k := Z.to_N (to_Z r)).
  assert (Hk : (k < len src)%N) by (unfold k; rewrite len_src; lia).
  set (x := lget src k). set (y := lget dst k).
  assert (Hx : (x < c)%N) by (apply src_lt; exact Hk).
  assert (Hy : (y < c)%N) by (apply dst_lt; exact Hk).
  pose proof (a_rng k Hk) as Ak. pose proof (b_rng k Hk) as Bk.
  assert (Es : to_Z xs.[r] = Z.of_N x) by (apply arr_get; [exact Hs | unfold NR in Hr; lia]).
  assert (Ed : to_Z xd.[r] = Z.of_N y) by (apply arr_get; [exact Hd | rewrite len_dst; lia]).
  assert (Ea : to_Z xa.[r] = Z.of_N (lget a k)) by (apply arr_get; [exact Ha | rewrite len_a; lia]).
  assert (Eb : to_Z xb.[r] = Z.of_N (lget b k)) by (apply arr_get; [exact Hb | rewrite len_b; lia]).
  assert (Eq : xs.[r] * xc + xd.[r] = qi x y) by (apply idx_q; assumption).
  unfold init_step. cbv zeta.
  change (@PArray.get int xs r) with (@PArray.get uint xs r).
  change (@PArray.get int xd r) with (@PArray.get uint xd r).
  change (@PArray.get int xa r) with (@PArray.get uint xa r).
  change (@PArray.get int xb r) with (@PArray.get uint xb r).
  rewrite Eq.
  pose proof (ratecell_ok xa.[r] xb.[r] ltac:(lia) ltac:(lia)) as Hrc.
  destruct (ratecell xa.[r] xb.[r]) as [[m e] n].
  rewrite Ea, Eb in Hrc. change (IZR (Z.of_N (lget b k)) / IZR (Z.of_N (lget a k)))%R with (rt k) in Hrc.
  pose proof HR as (L1 & L2 & L3 & L4 & L5 & HC).
  destruct (HC x y Hx Hy) as [P1 P2].
  pose proof (bd_val x y Hx Hy) as Bd.
  assert (Hbd : (to_Z (25 * qi x y) + 25 <= to_Z (PArray.length (tVT T)))%Z).
  { rewrite Bd, L5. pose proof (cell_lt x y Hx Hy) as CL. clear - CL. lia. }
  pose proof (vset_spec (25 * qi x y) (fun t => mlt xb.[r] primes.[t] - mlt xa.[r] primes.[t])
              (tVT T) Hbd) as VS.
  destruct VS as (V1 & V2 & V3).
  assert (Wr : Rep (wr_head T (qi x y) m e n (vset (25 * qi x y) xa.[r] xb.[r] (tVT T)))
                   (Dset D x y (Some [k]))).
  { apply Rep_write; [exact HR | exact Hx | exact Hy | | | | | |].
    - simpl wprod. rewrite Rmult_1_r. exact Hrc.
    - constructor; [exact Hk | constructor].
    - pose proof CZ_bounds as CB. clear - CB. change (Z.of_nat (List.length [k])) with 1%Z. lia.
    - unfold vset. rewrite V1. exact L5.
    - intros t Ht. unfold vset. rewrite <- idx_v by assumption.
      rewrite V2 by (apply t25_lt; exact Ht).
      rewrite sZ_rate by assumption. unfold wvec. simpl. fold k. ring.
    - intros i Hi. unfold vset. apply V3. rewrite Bd. exact Hi. }
  match goal with |- context [if ?B then wr_head _ _ _ _ _ _ else _] => set (bt := B) end.
  assert (Hbt : bt = true <-> match D x y with None => True | Some w => (wprod w < rt k)%R end).
  { unfold bt. rewrite P1. destruct (D x y) as [w |] eqn:Dxy; simpl; [| split; auto].
    destruct (P2 w eq_refl) as (Cw & Fw & Lw & Vw).
    apply oracle_ok; [apply rt_pos; exact Hk | apply wprod_pos; exact Fw | exact Hrc | exact Cw |].
    rewrite (Vp_ext _ (fun t => rv k t - wvec w t)%Z);
      [rewrite Vp_sub, Vp_rv, Vp_wvec by assumption; reflexivity |].
    intros tn Htn. unfold fdv. rewrite idx_v by assumption.
    pose proof (wvec_small w tn Lw) as W1. pose proof (rv_bound k tn) as W2.
    rewrite sZ_sub; [rewrite sZ_rate, Vw by assumption; reflexivity |].
    rewrite sZ_rate, Vw by assumption. apply small2; [apply rv_small | exact W1]. }
  exists (if bt then Dset D x y (Some [k]) else D). split.
  - destruct bt; [exact Wr | exact HR].
  - apply initinv_step; [exact Hk | split; assumption | exact Hbt].
Qed.

Lemma cc_val : to_Z (xc * xc) = (CZ * CZ)%Z.
Proof.
  rewrite Uint63.mul_spec, xc_val. pose proof CZ_bounds. apply Z.mod_small.
  change wB with 9223372036854775808%Z. nia.
Qed.

Lemma cc25_val : to_Z (25 * (xc * xc)) = (25 * (CZ * CZ))%Z.
Proof.
  rewrite Uint63.mul_spec, cc_val. pose proof CZ_bounds. apply Z.mod_small.
  change wB with 9223372036854775808%Z. change (to_Z 25) with 25%Z. nia.
Qed.

Lemma make_len_ok : forall n : int, (to_Z n <= 4194303)%Z -> (n <=? max_length) = true.
Proof. intros n H. rewrite Uint63.leb_spec. exact H. Qed.

Lemma Rep_T0 : Rep (mkT (PArray.make (xc * xc) false) (PArray.make (xc * xc) f_one)
                        (PArray.make (xc * xc) 0) (PArray.make (xc * xc) 0)
                        (PArray.make (25 * (xc * xc)) 0)) (fun _ _ => None).
Proof.
  pose proof CZ_bounds as CB.
  assert (E1 : (xc * xc <=? max_length) = true)
    by (apply make_len_ok; rewrite cc_val; clear - CB; nia).
  assert (E2 : (25 * (xc * xc) <=? max_length) = true)
    by (apply make_len_ok; rewrite cc25_val; clear - CB; nia).
  unfold Rep. simpl.
  rewrite blen_make, flen_make, !ilen_make, E1, E2.
  split; [exact cc_val |]. split; [exact cc_val |]. split; [exact cc_val |].
  split; [exact cc_val |]. split; [exact cc25_val |].
  intros x y _ _. unfold Cell. simpl. split; [apply bget_make | discriminate].
Qed.

Definition T1 : tabs :=
  loop (PArray.length xs) (fun _ _ => true) (init_step xc xs xd xa xb) 0
    (mkT (PArray.make (xc * xc) false) (PArray.make (xc * xc) f_one)
         (PArray.make (xc * xc) 0) (PArray.make (xc * xc) 0)
         (PArray.make (25 * (xc * xc)) 0)).

Lemma init_loop_ok : exists D, Rep T1 D /\ InitInv (len src) D.
Proof.
  unfold T1.
  pose (P := fun (r : int) (T : tabs) => (to_Z r <= NR)%Z /\
               exists D, Rep T D /\ InitInv (Z.to_N (to_Z r)) D).
  assert (HP : P (PArray.length xs) (loop (PArray.length xs) (fun _ _ => true)
       (init_step xc xs xd xa xb) 0
       (mkT (PArray.make (xc * xc) false) (PArray.make (xc * xc) f_one)
         (PArray.make (xc * xc) 0) (PArray.make (xc * xc) 0) (PArray.make (25 * (xc * xc)) 0)))).
  { apply for_inv.
    - change (to_Z 0) with 0%Z. pose proof (to_Z_bounded (PArray.length xs)). lia.
    - split; [change (to_Z 0) with 0%Z; unfold NR; lia |].
      exists (fun _ _ => None). split; [exact Rep_T0 |].
      split; [intros x y w E; discriminate | intros k Hk; change (to_Z 0) with 0%Z in Hk; lia].
    - intros j T Hj [Hj' (D & HR & HI)].
      assert (Hl : to_Z (PArray.length xs) = NR) by exact (len_arr xs src Hs).
      rewrite Hl in Hj.
      destruct (init_step_ok j T D ltac:(lia) HR HI) as (D' & HR' & HI').
      assert (Ej : to_Z (j + 1) = (to_Z j + 1)%Z) by (pose proof NR_bound; sia).
      split; [lia |]. exists D'. split; [exact HR' |].
      replace (Z.to_N (to_Z (j + 1))) with (Z.to_N (to_Z j) + 1)%N
        by (rewrite Ej; pose proof (to_Z_bounded j); lia).
      exact HI'. }
  destruct HP as [_ (D & HR & HI)]. exists D. split; [exact HR |].
  assert (Hl : to_Z (PArray.length xs) = NR) by exact (len_arr xs src Hs).
  rewrite Hl, <- len_src in HI. exact HI.
Qed.

(* -- the invariant of the closure -- *)
Definition Inv (k : N) (D : N -> N -> option (list N)) : Prop :=
  IS src dst k D /\ IC src dst a b k D /\ ID a b D.

Definition Prof : Prop :=
  exists u ks, ks <> [] /\ walk u u ks /\ (1 < wprod ks)%R.

Lemma init_Inv : forall D, InitInv (len src) D -> Inv 0 D.
Proof.
  intros D [I1 I2]. split; [| split].
  - intros x y w E. destruct (I1 _ _ _ E) as (k & -> & Hk & S1 & S2).
    split; [split; [simpl; auto | constructor; [exact Hk | constructor]] |].
    split; [discriminate |]. split; [| constructor].
    unfold simple. rewrite inter_single. split; [constructor | split; intros []].
  - intros x y W HW HN HB.
    assert (Ei : inter W = []).
    { destruct (inter W) as [| v l] eqn:E; [reflexivity |].
      unfold below in HB. inversion HB. lia. }
    destruct (inter_nil dst W HN Ei) as (k & ->).
    destruct HW as [[S1 S2] F]. inversion F; subst.
    destruct (I2 k H1) as (w & Ew & Lw). simpl in S2. subst y.
    exists w. split; [exact Ew |]. simpl. lra.
  - intros x w E. destruct (I1 _ _ _ E) as (k & -> & Hk & S1 & S2).
    pose proof (vi_diff _ _ _ _ _ Hv k Hk). congruence.
Qed.

Lemma leads_end : forall ks u v, leads src dst u v ks -> ks <> [] ->
  exists k, In k ks /\ v = lget dst k.
Proof.
  induction ks as [| k ks IH]; intros u v H N; [congruence |].
  destruct H as [_ H]. destruct ks as [| k' ks'].
  - simpl in H. exists k. split; [left; reflexivity | auto].
  - destruct (IH _ _ H ltac:(discriminate)) as (k0 & Hin & E). exists k0.
    split; [right; exact Hin | exact E].
Qed.

Lemma IS_bound : forall k D x y w, IS src dst k D -> D x y = Some w -> (x < c)%N /\ (y < c)%N.
Proof.
  intros k D x y w HS E. destruct (HS _ _ _ E) as ([HL HF] & HN & _ & _).
  destruct (leads_end w x y HL HN) as (k1 & Hin & ->).
  rewrite Forall_forall in HF.
  destruct w as [| k0 w]; [congruence |].
  destruct HL as [S1 _]. split.
  - rewrite <- S1. apply src_lt, HF. left; reflexivity.
  - apply dst_lt, HF, Hin.
Qed.

Lemma Inv_final : forall D, Inv c D -> ~ Prof.
Proof.
  intros D (HS & HC & HD) (u & ks & HN & HW & HP).
  destruct (HC u u ks HW HN) as (w & Ew & Lw).
  - unfold below. rewrite Forall_forall. intros v Hin.
    apply (inter_lt ks v (proj2 HW) Hin).
  - pose proof (HD u w Ew). lra.
Qed.

(* -- reading the cells -- *)
Lemma Rep_pr : forall T D x y, Rep T D -> (x < c)%N -> (y < c)%N -> (tPR T).[qi x y] = isS (D x y).
Proof. intros T D x y (_ & _ & _ & _ & _ & HC) Hx Hy. exact (proj1 (HC x y Hx Hy)). Qed.

Lemma Rep_some : forall T D x y w, Rep T D -> (x < c)%N -> (y < c)%N -> D x y = Some w ->
  cellF (tMA T).[qi x y] (tEX T).[qi x y] (tCN T).[qi x y] (wprod w) /\
  Forall (fun k => (k < len src)%N) w /\
  (Z.of_nat (List.length w) <= 2 * CZ + 2)%Z /\
  forall t, (t < 25)%nat -> sZ (tVT T).[vi x y t] = wvec w t.
Proof. intros T D x y w (_ & _ & _ & _ & _ & HC) Hx Hy E. exact (proj2 (HC x y Hx Hy) w E). Qed.

Lemma vec_sum : forall T D x y x' y' w1 w2 t, Rep T D ->
  (x < c)%N -> (y < c)%N -> (x' < c)%N -> (y' < c)%N ->
  D x y = Some w1 -> D x' y' = Some w2 -> (t < 25)%nat ->
  sZ ((tVT T).[25 * qi x y + of_Z (Z.of_nat t)] + (tVT T).[25 * qi x' y' + of_Z (Z.of_nat t)])
  = wvec (w1 ++ w2) t.
Proof.
  intros T D x y x' y' w1 w2 t HR Hx Hy Hx' Hy' E1 E2 Ht.
  destruct (Rep_some T D x y w1 HR Hx Hy E1) as (_ & _ & L1 & V1).
  destruct (Rep_some T D x' y' w2 HR Hx' Hy' E2) as (_ & _ & L2 & V2).
  rewrite !idx_v by assumption. rewrite wvec_app.
  rewrite sZ_add; rewrite V1, V2 by exact Ht; [reflexivity |].
  apply small2p; apply wvec_small; assumption.
Qed.

Lemma vec_diff : forall T D x y x' y' x'' y'' w1 w2 w0 t, Rep T D ->
  (x < c)%N -> (y < c)%N -> (x' < c)%N -> (y' < c)%N -> (x'' < c)%N -> (y'' < c)%N ->
  D x y = Some w1 -> D x' y' = Some w2 -> D x'' y'' = Some w0 -> (t < 25)%nat ->
  sZ ((tVT T).[25 * qi x y + of_Z (Z.of_nat t)] + (tVT T).[25 * qi x' y' + of_Z (Z.of_nat t)]
      - (tVT T).[25 * qi x'' y'' + of_Z (Z.of_nat t)])
  = (wvec (w1 ++ w2) t - wvec w0 t)%Z.
Proof.
  intros T D x y x' y' x'' y'' w1 w2 w0 t HR Hx Hy Hx' Hy' Hx'' Hy'' E1 E2 E0 Ht.
  pose proof (vec_sum T D x y x' y' w1 w2 t HR Hx Hy Hx' Hy' E1 E2 Ht) as S.
  destruct (Rep_some T D x y w1 HR Hx Hy E1) as (_ & _ & L1 & _).
  destruct (Rep_some T D x' y' w2 HR Hx' Hy' E2) as (_ & _ & L2 & _).
  destruct (Rep_some T D x'' y'' w0 HR Hx'' Hy'' E0) as (_ & _ & L0 & V0).
  rewrite sZ_sub; rewrite S; rewrite (idx_v x'' y'' t) by assumption; rewrite V0 by exact Ht;
    [reflexivity |].
  rewrite wvec_app. pose proof (wvec_small w1 t L1). pose proof (wvec_small w2 t L2).
  pose proof (wvec_small w0 t L0). clear - H H0 H1. lia.
Qed.

(* -- one stage, abstractly: the pairs before (i, j) are updated -- *)
Definition Dpart (k : N) (D0 : N -> N -> option (list N)) (i j : N) : N -> N -> option (list N) :=
  fun x y => if (x <? i)%N || ((x =? i)%N && (y <? j)%N) then upd a b k D0 x y else D0 x y.

Definition NE (k : N) (D0 : N -> N -> option (list N)) (i j : N) : Prop :=
  forall x w1 w2, ((x < i)%N \/ (x = i /\ (x < j)%N)) -> x <> k ->
    D0 x k = Some w1 -> D0 k x = Some w2 -> (wprod (w1 ++ w2) <= 1)%R.

Lemma upd_k : forall k D x y, (x = k \/ y = k) -> upd a b k D x y = D x y.
Proof.
  intros k D x y H. unfold upd.
  destruct H as [-> | ->]; rewrite N.eqb_refl; [reflexivity | rewrite Bool.orb_true_r; reflexivity].
Qed.

Lemma Dpart_k : forall k D0 i j x y, (x = k \/ y = k) -> Dpart k D0 i j x y = D0 x y.
Proof.
  intros k D0 i j x y H. unfold Dpart.
  destruct (_ || _); [apply upd_k; exact H | reflexivity].
Qed.

Lemma Dpart_ij : forall k D0 i j, Dpart k D0 i j i j = D0 i j.
Proof.
  intros k D0 i j. unfold Dpart. rewrite N.ltb_irrefl, N.eqb_refl, N.ltb_irrefl. reflexivity.
Qed.

Lemma Dpart_succ : forall k D0 i j x y,
  Dpart k D0 i (j + 1) x y =
  if (x =? i)%N && (y =? j)%N then upd a b k D0 i j else Dpart k D0 i j x y.
Proof.
  intros k D0 i j x y. unfold Dpart.
  destruct (N.eqb_spec x i) as [-> | Ex]; destruct (N.eqb_spec y j) as [-> | Ey]; simpl.
  - rewrite N.ltb_irrefl. replace (j <? j + 1)%N with true by (symmetry; apply N.ltb_lt; lia).
    reflexivity.
  - rewrite N.ltb_irrefl. simpl.
    destruct (N.ltb_spec y (j + 1)), (N.ltb_spec y j); try reflexivity; lia.
  - reflexivity.
  - reflexivity.
Qed.

Lemma NE_succ : forall k D0 i j, NE k D0 i j ->
  (i = j -> i <> k -> forall w1 w2, D0 i k = Some w1 -> D0 k i = Some w2 ->
     (wprod (w1 ++ w2) <= 1)%R) ->
  NE k D0 i (j + 1).
Proof.
  intros k D0 i j H Hdg x w1 w2 Hx Hk E1 E2.
  destruct Hx as [Hx | [-> Hx]].
  - apply (H x); auto.
  - destruct (N.eq_dec i j) as [-> | Nij].
    + apply Hdg; auto.
    + apply (H i); auto. right. split; [reflexivity | lia].
Qed.

Lemma blk_len : forall x y, (x < c)%N -> (y < c)%N ->
  (to_Z (25 * qi x y) + 25 <= 25 * (CZ * CZ))%Z.
Proof. intros x y Hx Hy. rewrite bd_val by assumption. pose proof (cell_lt x y Hx Hy). lia. Qed.

Lemma blk_disj : forall x y x' y', (x < c)%N -> (y < c)%N -> (x' < c)%N -> (y' < c)%N ->
  ~ (x = x' /\ y = y') ->
  (to_Z (25 * qi x' y') + 25 <= to_Z (25 * qi x y) \/ to_Z (25 * qi x y) + 25 <= to_Z (25 * qi x' y'))%Z.
Proof.
  intros x y x' y' Hx Hy Hx' Hy' N. rewrite !bd_val by assumption.
  destruct (Z.lt_total (Z.of_N x' * CZ + Z.of_N y') (Z.of_N x * CZ + Z.of_N y)) as [L | [E | L]].
  - left. lia.
  - exfalso. apply cell_inj in E; [| assumption ..]. destruct E. apply N; split; congruence.
  - right. lia.
Qed.

Lemma walk_D : forall k D x y w, IS src dst k D -> D x y = Some w -> walk x y w.
Proof. intros k D x y w HS E. exact (proj1 (HS _ _ _ E)). Qed.

Lemma len_D : forall k D x y w, IS src dst k D -> D x y = Some w ->
  (Z.of_nat (List.length w) <= CZ + 1)%Z.
Proof.
  intros k D x y w HS E. destruct (HS _ _ _ E) as (W & _ & Sm & _).
  exact (simple_len x y w W Sm).
Qed.

Lemma upd_new : forall k D0 x y w1 w2, x <> k -> y <> k -> D0 x k = Some w1 -> D0 k y = Some w2 ->
  upd a b k D0 x y = if better a b (w1 ++ w2) (D0 x y) then Some (w1 ++ w2) else D0 x y.
Proof.
  intros k D0 x y w1 w2 Hx Hy E1 E2. unfold upd.
  rewrite (proj2 (N.eqb_neq x k) Hx), (proj2 (N.eqb_neq y k) Hy). simpl.
  rewrite E1, E2. reflexivity.
Qed.

Lemma fw_j_ok : forall (k i j : int) (kN iN jN : N) D0 w1 (T : tabs),
  to_Z k = Z.of_N kN -> to_Z i = Z.of_N iN -> to_Z j = Z.of_N jN ->
  (kN < c)%N -> (iN < c)%N -> (jN < c)%N -> iN <> kN ->
  Inv kN D0 -> D0 iN kN = Some w1 ->
  Rep T (Dpart kN D0 iN jN) -> NE kN D0 iN jN ->
  (snd (fw_j xc k i j (T, false)) = true -> Prof) /\
  (snd (fw_j xc k i j (T, false)) = false ->
     Rep (fst (fw_j xc k i j (T, false))) (Dpart kN D0 iN (jN + 1)) /\ NE kN D0 iN (jN + 1)).
Proof.
  intros k i j kN iN jN D0 w1 T Ek Ei Ej Hk Hi Hj Nik HI E1 HR HN.
  pose proof HI as (HS & HC & HD).
  assert (HRik : Dpart kN D0 iN jN iN kN = Some w1) by (rewrite Dpart_k by auto; exact E1).
  unfold fw_j. cbv zeta. simpl fst.
  destruct (j =? k) eqn:Ejk.
  { apply Uint63.eqb_spec in Ejk. subst j. assert (jN = kN) by lia. subst jN.
    simpl. split; [discriminate | intros _]. split.
    - apply (Rep_ext T (Dpart kN D0 iN kN)); [| exact HR].
      intros x y _ _. rewrite Dpart_succ. destruct (_ && _) eqn:E; [| reflexivity].
      apply andb_prop in E as [E E']. apply N.eqb_eq in E, E'. subst.
      rewrite Dpart_k by auto. rewrite upd_k by auto. reflexivity.
    - apply NE_succ; [exact HN | intros F G; contradiction]. }
  apply Uint63.eqb_false_spec in Ejk.
  assert (Njk : jN <> kN) by (intros F; apply Ejk, to_Z_inj; lia).
  rewrite (idx_q k j kN jN Ek Ej Hk Hj).
  rewrite (Rep_pr _ _ kN jN HR Hk Hj), (Dpart_k _ _ _ _ kN jN (or_introl eq_refl)).
  destruct (D0 kN jN) as [w2 |] eqn:E2; cbn [isS].
  2: { simpl. split; [discriminate | intros _]. split.
       - apply (Rep_ext T (Dpart kN D0 iN jN)); [| exact HR].
         intros x y _ _. rewrite Dpart_succ. destruct (_ && _) eqn:E; [| reflexivity].
         apply andb_prop in E as [E E']. apply N.eqb_eq in E, E'. subst.
         rewrite Dpart_ij. unfold upd.
         rewrite (proj2 (N.eqb_neq _ _) Nik), (proj2 (N.eqb_neq _ _) Njk). simpl.
         rewrite E1, E2. reflexivity.
       - apply NE_succ; [exact HN |]. intros F _ w1' w2' _ G. subst jN. congruence. }
  rewrite (idx_q i k iN kN Ei Ek Hi Hk), (idx_q i j iN jN Ei Ej Hi Hj).
  destruct (Rep_some _ _ iN kN w1 HR Hi Hk HRik) as (C1 & F1 & L1 & V1).
  assert (HRkj : Dpart kN D0 iN jN kN jN = Some w2) by (rewrite Dpart_k by auto; exact E2).
  destruct (Rep_some _ _ kN jN w2 HR Hk Hj HRkj) as (C2 & F2 & L2 & V2).
  assert (F12 : Forall (fun k0 => (k0 < len src)%N) (w1 ++ w2)) by (apply Forall_app; auto).
  pose proof (wprod_pos _ F12) as P12.
  pose proof (mulcell_ok _ _ _ _ _ _ _ _ (Rlt_le _ _ (wprod_pos w1 F1))
                (Rlt_le _ _ (wprod_pos w2 F2)) C1 C2) as Cm.
  match goal with |- context [mulcell ?a1 ?a2 ?a3 ?a4 ?a5 ?a6] =>
    destruct (mulcell a1 a2 a3 a4 a5 a6) as [[m e] n] eqn:Em end.
  rewrite <- wprod_app in Cm.
  match goal with |- context [if ?B then (T, true) else _] => set (ex := B) end.
  assert (Hex : ex = true <-> (iN = jN /\ (1 < wprod (w1 ++ w2))%R)).
  { unfold ex. destruct (i =? j) eqn:Eij.
    - apply Uint63.eqb_spec in Eij. subst j. assert (iN = jN) by lia. subst jN.
      rewrite (oracle_ok m e n (wprod (w1 ++ w2)) f_one BIAS 0 1%R); [| exact P12 | lra | exact Cm |
        exact cellF_one |].
      + split; [intros L; split; [reflexivity | exact L] | intros [_ L]; exact L].
      + rewrite (Vp_ext _ (wvec (w1 ++ w2))); [rewrite Vp_wvec by exact F12; field |].
        intros tn Htn. unfold fdv.
        exact (vec_sum _ _ iN kN kN iN w1 w2 tn HR Hi Hk Hk Hi HRik HRkj Htn).
    - split; [discriminate | intros [F _]; exfalso].
      apply Uint63.eqb_false_spec in Eij. apply Eij, to_Z_inj. lia. }
  assert (Len12 : (Z.of_nat (List.length (w1 ++ w2)) <= 2 * CZ + 2)%Z).
  { rewrite length_app. pose proof (len_D _ _ _ _ _ HS E1). pose proof (len_D _ _ _ _ _ HS E2).
    clear - H H0. lia. }
  destruct ex eqn:Eex.
  { simpl. split; [intros _ | discriminate].
    destruct (proj1 Hex eq_refl) as [<- L]. exists iN, (w1 ++ w2).
    split; [destruct w1; [destruct (HS _ _ _ E1) as (_ & NN & _); congruence | discriminate] |].
    split; [| exact L].
    apply (walk_app src dst w1 w2 iN kN iN); eapply walk_D; eauto. }
  assert (Hdiag : iN = jN -> (wprod (w1 ++ w2) <= 1)%R).
  { intros Eq. destruct (Rlt_le_dec 1 (wprod (w1 ++ w2))) as [L | L]; [| exact L].
    assert (G : false = true) by (apply Hex; split; assumption). discriminate G. }
  assert (HNs : NE kN D0 iN (jN + 1)).
  { apply NE_succ; [exact HN |]. intros F _ w1' w2' G1 G2. subst jN.
    rewrite E1 in G1. rewrite E2 in G2. injection G1 as <-. injection G2 as <-.
    apply Hdiag. reflexivity. }
  match goal with |- context [if ?B then (wr_head _ _ _ _ _ _, false) else _] => set (bt := B) end.
  assert (Hbt : bt = better a b (w1 ++ w2) (D0 iN jN)).
  { unfold bt. rewrite (Rep_pr _ _ iN jN HR Hi Hj), Dpart_ij.
    destruct (D0 iN jN) as [w0 |] eqn:E0; cbn [isS better]; [| reflexivity].
    assert (HRij : Dpart kN D0 iN jN iN jN = Some w0) by (rewrite Dpart_ij; exact E0).
    destruct (Rep_some _ _ iN jN w0 HR Hi Hj HRij) as (C0 & F0 & L0 & V0).
    assert (O := oracle_ok m e n (wprod (w1 ++ w2)) _ _ _ (wprod w0)
      (fun t => (tVT T).[25 * qi iN kN + t] + (tVT T).[25 * qi kN jN + t] - (tVT T).[25 * qi iN jN + t])
      P12 (wprod_pos w0 F0) Cm C0).
    destruct (Rlt_dec (wprod w0) (wprod (w1 ++ w2))) as [L | L].
    - apply O; [| exact L].
      rewrite (Vp_ext _ (fun t => wvec (w1 ++ w2) t - wvec w0 t)%Z);
        [rewrite Vp_sub, !Vp_wvec by assumption; reflexivity |].
      intros tn Htn. unfold fdv.
      exact (vec_diff _ _ iN kN kN jN iN jN w1 w2 w0 tn HR Hi Hk Hk Hj Hi Hj HRik HRkj HRij Htn).
    - apply Bool.not_true_iff_false. intros G. apply L. apply O; [| exact G].
      rewrite (Vp_ext _ (fun t => wvec (w1 ++ w2) t - wvec w0 t)%Z);
        [rewrite Vp_sub, !Vp_wvec by assumption; reflexivity |].
      intros tn Htn. unfold fdv.
      exact (vec_diff _ _ iN kN kN jN iN jN w1 w2 w0 tn HR Hi Hk Hk Hj Hi Hj HRik HRkj HRij Htn). }
  pose proof (upd_new kN D0 iN jN w1 w2 Nik Njk E1 E2) as Hupd.
  destruct bt eqn:Ebt.
  - simpl. split; [discriminate | intros _]. split; [| exact HNs].
    pose proof HR as (R1 & R2 & R3 & R4 & R5 & _).
    assert (Nij_ik : ~ (iN = iN /\ jN = kN)) by tauto.
    assert (Nij_kj : ~ (iN = kN /\ jN = jN)) by tauto.
    destruct (vadd_spec (25 * qi iN jN) (25 * qi iN kN) (25 * qi kN jN) (tVT T))
      as (VA1 & VA2 & VA3).
    { rewrite R5. apply blk_len; assumption. }
    { rewrite R5. apply blk_len; assumption. }
    { rewrite R5. apply blk_len; assumption. }
    { apply blk_disj; assumption. }
    { apply blk_disj; assumption. }
    apply (Rep_ext _ (Dset (Dpart kN D0 iN jN) iN jN (Some (w1 ++ w2)))).
    + intros x y _ _. unfold Dset. rewrite Dpart_succ.
      destruct (_ && _) eqn:E; [| reflexivity].
      rewrite Hupd, <- Hbt. reflexivity.
    + apply Rep_write; [exact HR | exact Hi | exact Hj | exact Cm | exact F12 | exact Len12 | | |].
      * rewrite VA1. exact R5.
      * intros t Ht. rewrite <- idx_v by assumption. rewrite VA2 by (apply t25_lt; exact Ht).
        exact (vec_sum _ _ iN kN kN jN w1 w2 t HR Hi Hk Hk Hj HRik HRkj Ht).
      * intros i' Hi'. apply VA3. rewrite bd_val by assumption. exact Hi'.
  - simpl. split; [discriminate | intros _]. split; [| exact HNs].
    apply (Rep_ext T (Dpart kN D0 iN jN)); [| exact HR].
    intros x y _ _. rewrite Dpart_succ. destruct (_ && _) eqn:E; [| reflexivity].
    apply andb_prop in E as [E E']. apply N.eqb_eq in E, E'. subst.
    rewrite Dpart_ij, Hupd, <- Hbt. reflexivity.
Qed.

Lemma Dpart_i_succ : forall k D0 i x y,
  Dpart k D0 (i + 1) 0 x y = if (x =? i)%N then upd a b k D0 i y else Dpart k D0 i 0 x y.
Proof.
  intros k D0 i x y. unfold Dpart.
  destruct (N.ltb_spec y 0); [lia |]. rewrite !Bool.andb_false_r, !Bool.orb_false_r.
  destruct (N.eqb_spec x i) as [-> | E].
  - replace (i <? i + 1)%N with true by (symmetry; apply N.ltb_lt; lia). reflexivity.
  - destruct (N.ltb_spec x (i + 1)), (N.ltb_spec x i); try reflexivity; lia.
Qed.

Lemma Dpart_row_end : forall k D0 i x y, (y < c)%N ->
  Dpart k D0 i c x y = Dpart k D0 (i + 1) 0 x y.
Proof.
  intros k D0 i x y Hy. unfold Dpart.
  destruct (N.ltb_spec y 0); [lia |]. rewrite !Bool.andb_false_r, !Bool.orb_false_r.
  destruct (N.eqb_spec x i) as [-> | E].
  - rewrite N.ltb_irrefl. replace (y <? c)%N with true by (symmetry; apply N.ltb_lt; lia).
    replace (i <? i + 1)%N with true by (symmetry; apply N.ltb_lt; lia). reflexivity.
  - simpl. destruct (N.ltb_spec x (i + 1)), (N.ltb_spec x i); try reflexivity; lia.
Qed.

Lemma Dpart_zero : forall k D0 x y, Dpart k D0 0 0 x y = D0 x y.
Proof. intros. unfold Dpart. destruct (N.ltb_spec x 0); [lia |]. destruct (N.ltb_spec y 0); [lia |].
  rewrite Bool.andb_false_r. reflexivity. Qed.

Lemma Dpart_full : forall k D0 x y, (x < c)%N -> Dpart k D0 c 0 x y = upd a b k D0 x y.
Proof. intros k D0 x y Hx. unfold Dpart. replace (x <? c)%N with true by (symmetry; apply N.ltb_lt; lia).
  reflexivity. Qed.

Lemma NE_row : forall k D0 i, NE k D0 i c -> (i < c)%N -> NE k D0 (i + 1) 0.
Proof.
  intros k D0 i H Hi x w1 w2 Hx. apply H. destruct Hx as [Hx | [_ Hx]]; [| lia].
  destruct (N.eq_dec x i) as [-> | E]; [right; split; [reflexivity | exact Hi] | left; lia].
Qed.

Lemma NE_skip : forall k D0 i, NE k D0 i 0 -> (i = k \/ D0 i k = None) -> NE k D0 (i + 1) 0.
Proof.
  intros k D0 i H Hsk x w1 w2 Hx Hk E1 E2. destruct Hx as [Hx | [_ Hx]]; [| lia].
  destruct (N.eq_dec x i) as [-> | E].
  - destruct Hsk as [-> | Hsk]; [contradiction | congruence].
  - apply (H x); auto. left. lia.
Qed.

Lemma fw_i_ok : forall (k i : int) (kN iN : N) D0 (T : tabs),
  to_Z k = Z.of_N kN -> to_Z i = Z.of_N iN -> (kN < c)%N -> (iN < c)%N -> Inv kN D0 ->
  Rep T (Dpart kN D0 iN 0) -> NE kN D0 iN 0 ->
  (snd (fw_i xc k i (T, false)) = true -> Prof) /\
  (snd (fw_i xc k i (T, false)) = false ->
     Rep (fst (fw_i xc k i (T, false))) (Dpart kN D0 (iN + 1) 0) /\ NE kN D0 (iN + 1) 0).
Proof.
  intros k i kN iN D0 T Ek Ei Hk Hi HI HR HN.
  unfold fw_i. simpl fst.
  destruct (i =? k) eqn:Eik.
  { apply Uint63.eqb_spec in Eik. subst i. assert (iN = kN) by lia. subst iN.
    simpl. split; [discriminate | intros _]. split.
    - apply (Rep_ext T (Dpart kN D0 kN 0)); [| exact HR].
      intros x y _ _. rewrite Dpart_i_succ. destruct (N.eqb_spec x kN) as [-> |]; [| reflexivity].
      rewrite upd_k by auto. unfold Dpart. rewrite N.ltb_irrefl. destruct (N.ltb_spec y 0); [lia |].
      rewrite Bool.andb_false_r. reflexivity.
    - apply NE_skip; [exact HN | left; reflexivity]. }
  apply Uint63.eqb_false_spec in Eik.
  assert (Nik : iN <> kN) by (intros F; apply Eik, to_Z_inj; lia).
  rewrite (idx_q i k iN kN Ei Ek Hi Hk), (Rep_pr _ _ iN kN HR Hi Hk),
    (Dpart_k _ _ _ _ iN kN (or_intror eq_refl)).
  destruct (D0 iN kN) as [w1 |] eqn:E1; cbn [isS].
  2: { simpl. split; [discriminate | intros _]. split.
       - apply (Rep_ext T (Dpart kN D0 iN 0)); [| exact HR].
         intros x y _ _. rewrite Dpart_i_succ. destruct (N.eqb_spec x iN) as [-> |]; [| reflexivity].
         unfold upd. rewrite (proj2 (N.eqb_neq _ _) Nik). rewrite E1. simpl.
         destruct (y =? kN)%N; unfold Dpart; rewrite N.ltb_irrefl, N.eqb_refl;
           destruct (N.ltb_spec y 0); try lia; reflexivity.
       - apply NE_skip; [exact HN | right; exact E1]. }
  pose (PJ := fun (j : int) (s : tabs * bool) =>
    (to_Z j <= CZ)%Z /\
    (snd s = true -> Prof) /\
    (snd s = false -> Rep (fst s) (Dpart kN D0 iN (Z.to_N (to_Z j))) /\
                      NE kN D0 iN (Z.to_N (to_Z j)))).
  assert (Hxc : to_Z xc = CZ) by exact xc_val.
  destruct (loop_inv PJ xc 0 (fun _ s => negb (snd s)) (fw_j xc k i) (T, false))
    as (j' & Hj' & HP & Hend).
  { change (to_Z 0) with 0%Z. pose proof CZ_bounds. lia. }
  { split; [change (to_Z 0) with 0%Z; pose proof CZ_bounds; lia |].
    split; [discriminate | intros _]. simpl. split; assumption. }
  { intros j [T' f] Hj (Hjc & P1 & P2) Hcont. simpl in Hcont. destruct f; [discriminate |].
    destruct (P2 eq_refl) as [HR' HN'].
    change (to_Z 0) with 0%Z in Hj. rewrite Hxc in Hj.
    assert (Ej1 : to_Z (j + 1) = (to_Z j + 1)%Z) by (pose proof CZ_bounds; sia).
    destruct (fw_j_ok k i j kN iN (Z.to_N (to_Z j)) D0 w1 T' Ek Ei ltac:(lia) Hk Hi
                ltac:(unfold CZ in *; lia) Nik HI E1 HR' HN') as [Q1 Q2].
    split; [lia |]. split; [exact Q1 |].
    replace (Z.to_N (to_Z (j + 1))) with (Z.to_N (to_Z j) + 1)%N by lia.
    exact Q2. }
  destruct HP as (_ & P1 & P2). split; [exact P1 |]. intros Hf.
  destruct (P2 Hf) as [HR' HN'].
  assert (Ej : to_Z j' = CZ).
  { destruct Hend as [E | [_ E]]; [rewrite Hxc in E; exact E |].
    rewrite Hf in E. discriminate. }
  rewrite Ej in HR', HN'. replace (Z.to_N CZ) with c in HR', HN' by (unfold CZ; lia).
  split.
  - apply (Rep_ext _ (Dpart kN D0 iN c)); [| exact HR'].
    intros x y _ Hy. apply Dpart_row_end. exact Hy.
  - apply NE_row; assumption.
Qed.

Lemma fw_k_ok : forall (k : int) (kN : N) D (T : tabs),
  to_Z k = Z.of_N kN -> (kN < c)%N -> Inv kN D -> Rep T D ->
  (snd (fw_k xc k (T, false)) = true -> Prof) /\
  (snd (fw_k xc k (T, false)) = false ->
     exists D', Rep (fst (fw_k xc k (T, false))) D' /\ Inv (kN + 1) D').
Proof.
  intros k kN D T Ek Hk HI HR. unfold fw_k.
  pose (PI := fun (i : int) (s : tabs * bool) =>
    (to_Z i <= CZ)%Z /\
    (snd s = true -> Prof) /\
    (snd s = false -> Rep (fst s) (Dpart kN D (Z.to_N (to_Z i)) 0) /\
                      NE kN D (Z.to_N (to_Z i)) 0)).
  assert (Hxc : to_Z xc = CZ) by exact xc_val.
  destruct (loop_inv PI xc 0 (fun _ s => negb (snd s)) (fw_i xc k) (T, false))
    as (i' & Hi' & HP & Hend).
  { change (to_Z 0) with 0%Z. pose proof CZ_bounds. lia. }
  { split; [change (to_Z 0) with 0%Z; pose proof CZ_bounds; lia |].
    split; [discriminate | intros _]. simpl. split.
    - apply (Rep_ext T D); [| exact HR]. intros x y _ _. symmetry. apply Dpart_zero.
    - intros x w1 w2 Hx. change (Z.to_N (to_Z 0)) with 0%N in Hx. lia. }
  { intros i [T' f] Hi (Hic & P1 & P2) Hcont. simpl in Hcont. destruct f; [discriminate |].
    destruct (P2 eq_refl) as [HR' HN'].
    change (to_Z 0) with 0%Z in Hi. rewrite Hxc in Hi.
    assert (Ei1 : to_Z (i + 1) = (to_Z i + 1)%Z) by (pose proof CZ_bounds; sia).
    destruct (fw_i_ok k i kN (Z.to_N (to_Z i)) D T' Ek ltac:(lia) Hk
                ltac:(unfold CZ in *; lia) HI HR' HN') as [Q1 Q2].
    split; [lia |]. split; [exact Q1 |].
    replace (Z.to_N (to_Z (i + 1))) with (Z.to_N (to_Z i) + 1)%N by lia.
    exact Q2. }
  destruct HP as (_ & P1 & P2). split; [exact P1 |]. intros Hf.
  destruct (P2 Hf) as [HR' HN'].
  assert (Ei : to_Z i' = CZ).
  { destruct Hend as [E | [_ E]]; [rewrite Hxc in E; exact E |].
    rewrite Hf in E. discriminate. }
  rewrite Ei in HR', HN'. replace (Z.to_N CZ) with c in HR', HN' by (unfold CZ; lia).
  destruct HI as (HS & HC & HD).
  assert (Hne : noexit a b kN D).
  { intros x w1 w2 Hx E1 E2. apply (HN' x); auto. left.
    exact (proj1 (IS_bound _ _ _ _ _ HS E1)). }
  exists (upd a b kN D). split.
  - apply (Rep_ext _ (Dpart kN D c 0)); [| exact HR'].
    intros x y Hx _. apply Dpart_full. exact Hx.
  - split; [apply IS_step; assumption |]. split; [apply IC_step; assumption |].
    apply ID_step; assumption.
Qed.

Lemma closure_ok : snd (loop xc (fun _ s => negb (snd s)) (fw_k xc) 0 (T1, false)) = true <-> Prof.
Proof.
  pose (PK := fun (k : int) (s : tabs * bool) =>
    (to_Z k <= CZ)%Z /\
    (snd s = true -> Prof) /\
    (snd s = false -> exists D, Rep (fst s) D /\ Inv (Z.to_N (to_Z k)) D)).
  assert (Hxc : to_Z xc = CZ) by exact xc_val.
  destruct (loop_inv PK xc 0 (fun _ s => negb (snd s)) (fw_k xc) (T1, false))
    as (k' & Hk' & HP & Hend).
  { change (to_Z 0) with 0%Z. pose proof CZ_bounds. lia. }
  { split; [change (to_Z 0) with 0%Z; pose proof CZ_bounds; lia |].
    split; [discriminate | intros _]. simpl.
    destruct init_loop_ok as (D & HR & HI). exists D. split; [exact HR |].
    exact (init_Inv D HI). }
  { intros k [T' f] Hk (Hkc & P1 & P2) Hcont. simpl in Hcont. destruct f; [discriminate |].
    destruct (P2 eq_refl) as (D & HR' & HI').
    change (to_Z 0) with 0%Z in Hk. rewrite Hxc in Hk.
    assert (Ek1 : to_Z (k + 1) = (to_Z k + 1)%Z) by (pose proof CZ_bounds; sia).
    destruct (fw_k_ok k (Z.to_N (to_Z k)) D T' ltac:(lia) ltac:(unfold CZ in *; lia) HI' HR')
      as [Q1 Q2].
    split; [lia |]. split; [exact Q1 |].
    replace (Z.to_N (to_Z (k + 1))) with (Z.to_N (to_Z k) + 1)%N by lia.
    exact Q2. }
  destruct HP as (_ & P1 & P2).
  destruct (snd (loop xc (fun _ s => negb (snd s)) (fw_k xc) 0 (T1, false))) eqn:Ef.
  - split; [intros _; apply P1; reflexivity | reflexivity].
  - split; [discriminate | intros HPr]. exfalso.
    destruct (P2 eq_refl) as (D & _ & HI).
    assert (Ek : to_Z k' = CZ).
    { destruct Hend as [E | [_ E]]; [rewrite Hxc in E; exact E |].
      try rewrite Ef in E; discriminate. }
    rewrite Ek in HI. replace (Z.to_N CZ) with c in HI by (unfold CZ; lia).
    exact (Inv_final D HI HPr).
Qed.

(* -- the spec's profitability is a closed walk of product above 1 -- *)
Lemma Q2R_inject : forall z, Q2R (inject_Z z) = IZR z.
Proof. intros z. unfold Q2R. simpl. rewrite Rinv_1. ring. Qed.

Lemma Q2R_rate : forall k, Q2R (inject_Z (Z.of_N (lget b k)) / inject_Z (Z.of_N (lget a k)))%Q = rt k.
Proof.
  intros k. unfold arbitrage_implem.rt.
  destruct (Z.eq_dec (Z.of_N (lget a k)) 0) as [E | E].
  - rewrite E. unfold Qdiv. change (Qinv (inject_Z 0)) with 0%Q.
    rewrite Q2R_mult. unfold Rdiv. rewrite Rinv_0. unfold Q2R at 2. simpl. ring.
  - rewrite Q2R_div.
    + rewrite !Q2R_inject. reflexivity.
    + unfold Qeq. simpl. lia.
Qed.

Lemma amount_R : forall ks x, Q2R (amount_after a b ks x) = (Q2R x * wprod ks)%R.
Proof.
  induction ks as [| k ks IH]; intros x; simpl; [ring |].
  rewrite IH, Q2R_mult, Q2R_rate. ring.
Qed.

Lemma Prof_iff : Prof <-> profitable src dst a b.
Proof.
  split.
  - intros (u & ks & HN & [HL HF] & HP). exists u, ks, 1%Q.
    split; [exact HN |]. split; [exact HF |]. split; [exact HL |]. split; [reflexivity |].
    apply Rlt_Qlt. rewrite amount_R. unfold Q2R. simpl. lra.
  - intros (u & ks & x & HN & HF & HL & Hx & Ha').
    exists u, ks. split; [exact HN |]. split; [split; assumption |].
    apply Qlt_Rlt in Hx, Ha'. rewrite amount_R in Ha'.
    unfold Q2R at 1 in Hx. simpl in Hx. rewrite Rmult_0_l in Hx.
    apply (Rmult_lt_reg_l (Q2R x)); [exact Hx |]. lra.
Qed.

Lemma arbitrage_main : arbitrage_impl xc xs xd xa xb = true <-> profitable src dst a b.
Proof.
  rewrite <- Prof_iff, <- closure_ok. unfold arbitrage_impl. cbv zeta. reflexivity.
Qed.

End Main.

(* ------------------------------------------------------------------ *)
(* The spec's items, at top level                                      *)
(* ------------------------------------------------------------------ *)

(* The spec's match on the boolean answer, from the iff form. *)
Lemma bool_match_of_iff : forall (b : bool) (P : Prop),
  (b = true <-> P) -> match b with true => P | false => ~ P end.
Proof.
  intros [|] P H; [apply H; reflexivity | intros HP; apply H in HP; discriminate].
Qed.

Definition arbitrage : uint -> array uint -> array uint -> array uint -> array uint -> bool :=
  arbitrage_impl.

Lemma arbitrage_correct :
  forall (c : N) (src dst a b : list N)
         (xc : uint) (xsrc xdst xa xb : array uint),
  valid_input c src dst a b ->
  repr xc c -> repr xsrc src -> repr xdst dst -> repr xa a -> repr xb b ->
  exists o : bool, repr (arbitrage xc xsrc xdst xa xb) o /\
                   arbitrage_spec c src dst a b o.
Proof.
  intros c src dst a b xc xs xd xa xb Hv Hc Hs Hd Ha Hb.
  exists (arbitrage_impl xc xs xd xa xb). split; [reflexivity |].
  unfold arbitrage_spec.
  exact (arbitrage_main c src dst a b xc xs xd xa xb Hv Hc Hs Hd Ha Hb).
Qed.
