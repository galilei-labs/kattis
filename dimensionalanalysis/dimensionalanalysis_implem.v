(* Implementation of dimensionalanalysis (dimensionalanalysis.spec).

   Code.  ONE exact, fraction-free Gauss-Jordan elimination of the n x m
   exponent table, in place on one flat [array Z] (cell (i, j) at i*m + j),
   threaded linearly.  Columns c = 0 .. m-1 in order: the pivot is the first
   row not yet used as a pivot row (flags in one flat [array bool]) with a
   nonzero entry in column c; every other row i with f = T[i][c] <> 0 becomes
   p * row i - f * row s (p the pivot), then is divided by the gcd of its
   entries ([StdGalilei.bigint.zgcd]) to keep the entries at the size of minors.
   At the end the table is a reduced echelon form up to row scaling, and a
   quantity is forced dimensionless exactly when some row has a single
   nonzero entry, so [valid] answers "no row has exactly one nonzero".
   Entries are converted from sint to Z by a nat-free binary recursion
   ([sconv]; Uint63.to_Z recurses on a nat).  Indices, lengths and counters
   are Uint63; the only bignums are the cells and the arithmetic on them.

   Termination: every loop is the one combinator [for_] (lo .. hi - 1),
   structural on an erased [Acc (Zwf 0) (gap hi i)]; [uconv] on an erased
   [Acc (Zwf 0) (φ x)].

   Proof.  [for_spec] is the one loop rule (an invariant P indexed by φ i).
   On the math side the table is a Z-indexed matrix [cell T m]; [Inv]
   says that it has the same rational solutions as the input ([sol]) and
   the pivot structure [PivOK] (used rows have a pivot column < c, alone
   nonzero in it; other rows are zero on the columns < c).  [inv_elim] /
   [inv_skip] carry it across a column; [final_iff] reads the answer off
   at c = m, building the witness assignment [dk] (one free column set to
   1, pivot columns solved).  [satisfies_iff] / [free_iff] connect [sol]
   to the spec's [satisfies] / [free_quantity]. *)

From Dimensionalanalysis.spec Require Import Prelude.
From StdGalilei Require Import repr.
From StdGalilei Require Import bigint.
From Stdlib Require Import ZArith NArith QArith List Uint63 PArray ZifyUint63 Lia Zwf.
From Stdlib Require Sint63.
Import ListNotations.

Open Scope uint63_scope.
Open Scope array_scope.

Unset Lia Cache.

Ltac sia := zify; Z.to_euclidean_division_equations; lia.

(* ------------------------------------------------------------------ *)
(* The termination device and the one loop                             *)
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

(* s threaded through f i, for i = lo .. hi - 1. *)
Fixpoint loop {S : Type} (f : int -> S -> S) (hi i : int) (s : S)
    (H : Acc (Zwf 0) (gap hi i)) {struct H} : S :=
  match bdec (i <? hi) with
  | left Hi => loop f hi (i + 1) (f i s) (Acc_inv H (dec_step hi i Hi))
  | right _ => s
  end.

Definition for_ {S : Type} (lo hi : int) (s : S) (f : int -> S -> S) : S :=
  loop f hi lo s (Zwf_well_founded 0 (gap hi lo)).

(* ------------------------------------------------------------------ *)
(* sint -> Z, nat-free (Uint63.to_Z recurses on a nat)                 *)
(* ------------------------------------------------------------------ *)

Lemma half_dec : forall x : int, (x =? 0) = false -> Zwf 0 (φ (x / 2)) (φ x).
Proof.
  intros x H. rewrite eqb_false_spec in H.
  assert ((φ x) <> 0%Z) by (intro E; apply H; apply to_Z_inj; exact E).
  pose proof (to_Z_bounded x). unfold Zwf. rewrite div_spec.
  change (φ 2) with 2%Z. split; [lia|]. apply Z.div_lt; lia.
Qed.

Fixpoint uconv (x : int) (H : Acc (Zwf 0) (φ x)) {struct H} : Z :=
  match bdec (x =? 0) with
  | left _ => 0%Z
  | right Hx =>
      (2 * uconv (x / 2)%uint63 (Acc_inv H (half_dec x Hx))
       + (if (x mod 2 =? 0)%uint63 then 0 else 1))%Z
  end.

Definition sconv (x : sint) : Z :=
  if x <? 4611686018427387904 then uconv x (Zwf_well_founded 0 _)
  else (- uconv (0 - x) (Zwf_well_founded 0 _))%Z.

(* ------------------------------------------------------------------ *)
(* The program                                                         *)
(* ------------------------------------------------------------------ *)

(* the flat n x m table of Z, cell (i, j) at i * m + j *)
Definition ztab (n m : int) (xe : array (array sint)) : array Z :=
  for_ 0 n (PArray.make (n * m) 0%Z) (fun i T =>
    let row := xe.[i] in
    for_ 0 m T (fun j T => T.[i * m + j <- sconv row.[j]])).

(* row i := p * row i - f * row s *)
Definition upd_row (m i s : int) (p f : Z) (T : array Z) : array Z :=
  for_ 0 m T (fun j T =>
    T.[i * m + j <- (p * T.[i * m + j] - f * T.[s * m + j])%Z]).

Definition row_gcd (m i : int) (T : array Z) : Z :=
  for_ 0 m 0%Z (fun j g => zgcd g T.[i * m + j]).

Definition div_row (m i : int) (g : Z) (T : array Z) : array Z :=
  for_ 0 m T (fun j T => T.[i * m + j <- (T.[i * m + j] / g)%Z]).

Definition norm_row (m i : int) (T : array Z) : array Z :=
  let g := row_gcd m i T in
  if (1 <? g)%Z then div_row m i g T else T.

(* eliminate column c from every row but the pivot row s *)
Definition elim_rows (n m s c : int) (T : array Z) : array Z :=
  let p := T.[s * m + c] in
  for_ 0 n T (fun i T =>
    if i =? s then T
    else
      let f := T.[i * m + c] in
      if (f =? 0)%Z then T else norm_row m i (upd_row m i s p f T)).

(* the first row not yet a pivot row with a nonzero entry in column c,
   or n *)
Definition find_piv (n m c : int) (T : array Z) (U : array bool) : int :=
  for_ 0 n n (fun i r =>
    if r =? n then
      (if U.[i] then r else if (T.[i * m + c] =? 0)%Z then r else i)
    else r).

Definition col_step (n m : int) (c : int) (st : array Z * array bool)
    : array Z * array bool :=
  let T := fst st in
  let U := snd st in
  let s := find_piv n m c T U in
  if s =? n then st else (elim_rows n m s c T, U.[s <- true]).

Definition count_nz (m i : int) (T : array Z) : int :=
  for_ 0 m 0 (fun j k => if (T.[i * m + j] =? 0)%Z then k else k + 1).

Definition valid_impl (xm : uint) (xe : array (array sint)) : bool :=
  let n := PArray.length xe in
  let m := xm in
  let st := for_ 0 m (ztab n m xe, PArray.make n false) (col_step n m) in
  let T := fst st in
  for_ 0 n true (fun i b => if b then negb (count_nz m i T =? 1) else false).

(* ------------------------------------------------------------------ *)
(* Prop side: the loop                                                 *)
(* ------------------------------------------------------------------ *)

Lemma loop_eq : forall {S} (f : int -> S -> S) hi i s H,
  loop f hi i s H =
  match bdec (i <? hi) with
  | left Hi => loop f hi (i + 1) (f i s) (Acc_inv H (dec_step hi i Hi))
  | right _ => s
  end.
Proof. intros. destruct H. reflexivity. Qed.

Lemma loop_spec : forall {S} (P : Z -> S -> Prop) (f : int -> S -> S) (lo hi : int),
  (forall (i : int) (t : S), ((φ lo) <= (φ i) < (φ hi))%Z -> P (φ i) t -> P ((φ i) + 1)%Z (f i t)) ->
  forall z (i : int) (s : S) (H : Acc (Zwf 0) (gap hi i)), gap hi i = z ->
  ((φ lo) <= (φ i) <= (φ hi))%Z -> P (φ i) s -> P (φ hi) (loop f hi i s H).
Proof.
  intros S P f lo hi Hf z.
  induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros i s H Hz Hi Hs. rewrite loop_eq.
  destruct (bdec (i <? hi)) as [Hl | Hl].
  - pose proof Hl as Hl'. rewrite ltb_spec in Hl'.
    assert (H1 : (φ (i + 1)) = ((φ i) + 1)%Z) by sia.
    eapply IH; [ rewrite <- Hz; apply dec_step; exact Hl | reflexivity | lia | ].
    rewrite H1. apply Hf; [lia | exact Hs].
  - rewrite <- Bool.not_true_iff_false, ltb_spec in Hl.
    replace (φ hi) with (φ i) by lia. exact Hs.
Qed.

Lemma for_spec : forall {S} (P : Z -> S -> Prop) (lo hi : int) (s : S) (f : int -> S -> S),
  ((φ lo) <= (φ hi))%Z -> P (φ lo) s ->
  (forall (i : int) (t : S), ((φ lo) <= (φ i) < (φ hi))%Z -> P (φ i) t -> P ((φ i) + 1)%Z (f i t)) ->
  P (φ hi) (for_ lo hi s f).
Proof.
  intros S P lo hi s f Hlh Hs Hf. unfold for_.
  eapply loop_spec; [exact Hf | reflexivity | lia | exact Hs].
Qed.

(* ------------------------------------------------------------------ *)
(* Prop side: sconv                                                    *)
(* ------------------------------------------------------------------ *)

Lemma uconv_eq : forall (x : int) (H : Acc (Zwf 0) (φ x)),
  uconv x H =
  match bdec (x =? 0) with
  | left _ => 0%Z
  | right Hx =>
      (2 * uconv (x / 2)%uint63 (Acc_inv H (half_dec x Hx))
       + (if (x mod 2 =? 0)%uint63 then 0 else 1))%Z
  end.
Proof. intros. destruct H. reflexivity. Qed.

Lemma uconv_spec : forall z (x : int) (H : Acc (Zwf 0) (φ x)), (φ x) = z -> uconv x H = (φ x).
Proof.
  intros z. induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros x H Hz. rewrite uconv_eq.
  destruct (bdec (x =? 0)) as [E | E].
  - rewrite eqb_spec in E. subst x. reflexivity.
  - rewrite (IH (φ (x / 2))); [ | rewrite <- Hz; apply half_dec; exact E | reflexivity].
    rewrite div_spec. change (φ 2) with 2%Z.
    destruct (x mod 2 =? 0) eqn:M.
    + rewrite eqb_spec in M. apply (f_equal to_Z) in M. rewrite mod_spec in M.
      change (φ 2) with 2%Z in M. change (φ 0) with 0%Z in M.
      pose proof (Z.div_mod (φ x) 2 ltac:(lia)). lia.
    + rewrite eqb_false_spec in M.
      assert (M' : ((φ x) mod 2 <> 0)%Z).
      { intro F. apply M. apply to_Z_inj. rewrite mod_spec. exact F. }
      pose proof (Z.div_mod (φ x) 2 ltac:(lia)).
      pose proof (Z.mod_pos_bound (φ x) 2 ltac:(lia)). lia.
Qed.

Lemma sconv_spec : forall x : sint, sconv x = Sint63.to_Z x.
Proof.
  intros x. unfold sconv, Sint63.to_Z.
  rewrite !(uconv_spec _ _ _ eq_refl).
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* Prop side: the flat table                                           *)
(* ------------------------------------------------------------------ *)

Lemma wB_val : wB = 9223372036854775808%Z.
Proof. reflexivity. Qed.

Lemma max_length_val : (φ PArray.max_length) = 4194303%Z.
Proof. reflexivity. Qed.

Lemma alength_bound : forall {A} (t : array A), ((φ (PArray.length t)) <= 4194303)%Z.
Proof.
  intros A t. pose proof (leb_length A t) as H.
  rewrite leb_spec, max_length_val in H. exact H.
Qed.

Lemma zget_set_same : forall (t : array Z) (i : int) (b : Z),
  (i <? PArray.length t) = true -> t.[i <- b].[i] = b.
Proof. intros t i b H. exact (get_set_same Z t i b H). Qed.

Lemma zget_set_other : forall (t : array Z) (i j : int) (b : Z),
  i <> j -> t.[i <- b].[j] = t.[j].
Proof. intros t i j b H. exact (get_set_other Z t i j b H). Qed.

Lemma zlength_set : forall (t : array Z) (i : int) (b : Z),
  PArray.length t.[i <- b] = PArray.length t.
Proof. intros t i b. exact (length_set Z t i b). Qed.

Lemma bget_set_same : forall (t : array bool) (i : int) (b : bool),
  (i <? PArray.length t) = true -> t.[i <- b].[i] = b.
Proof. intros t i b H. exact (get_set_same bool t i b H). Qed.

Lemma bget_set_other : forall (t : array bool) (i j : int) (b : bool),
  i <> j -> t.[i <- b].[j] = t.[j].
Proof. intros t i j b H. exact (get_set_other bool t i j b H). Qed.

Lemma blength_set : forall (t : array bool) (i : int) (b : bool),
  PArray.length t.[i <- b] = PArray.length t.
Proof. intros t i b. exact (length_set bool t i b). Qed.

Lemma blength_make : forall (k : int) (b : bool),
  PArray.length (PArray.make k b) = if k <=? PArray.max_length then k else PArray.max_length.
Proof. intros k b. exact (length_make bool k b). Qed.

Lemma bget_make : forall (k i : int) (b : bool), (PArray.make k b).[i] = b.
Proof. intros k i b. exact (get_make bool b k i). Qed.

(* cell (i, j) of the flat table T of width m *)
Definition cell (T : array Z) (m i j : Z) : Z := T.[of_Z (i * m + j)].

Lemma idx_eq : forall i m j : int,
  (0 <= (φ i) * (φ m) + (φ j) < 4194304)%Z -> i * m + j = of_Z ((φ i) * (φ m) + (φ j)).
Proof.
  intros i m j Hb. apply to_Z_inj. rewrite of_Z_spec, add_spec, mul_spec.
  pose proof (to_Z_bounded i). pose proof (to_Z_bounded m). pose proof (to_Z_bounded j).
  rewrite wB_val in *.
  rewrite (Z.mod_small ((φ i) * (φ m))) by nia.
  rewrite Z.mod_small by lia. reflexivity.
Qed.

Lemma get_idx : forall (T : array Z) (i m j : int),
  (0 <= (φ i) * (φ m) + (φ j) < 4194304)%Z -> T.[i * m + j] = cell T (φ m) (φ i) (φ j).
Proof. intros T i m j Hb. unfold cell. rewrite idx_eq by exact Hb. reflexivity. Qed.

Lemma set_idx : forall (T : array Z) (i m j : int) v,
  (0 <= (φ i) * (φ m) + (φ j) < 4194304)%Z ->
  T.[i * m + j <- v] = T.[of_Z ((φ i) * (φ m) + (φ j)) <- v].
Proof. intros T i m j v Hb. rewrite idx_eq by exact Hb. reflexivity. Qed.

Lemma idx_inj : forall i i' j j' m : Z,
  (0 <= j < m)%Z -> (0 <= j' < m)%Z -> (i * m + j = i' * m + j')%Z -> i = i' /\ j = j'.
Proof.
  intros i i' j j' m Hj Hj' E.
  assert (i = i') by nia. subst. split; lia.
Qed.

Lemma of_Z_inj_small : forall a b : Z,
  (0 <= a < wB)%Z -> (0 <= b < wB)%Z -> of_Z a = of_Z b -> a = b.
Proof.
  intros a b Ha Hb E. apply (f_equal to_Z) in E. rewrite !of_Z_spec in E.
  rewrite !Z.mod_small in E by lia. exact E.
Qed.

Lemma cell_set : forall (T : array Z) (n m i j i' j' v : Z),
  (φ (PArray.length T)) = (n * m)%Z ->
  (0 <= i < n)%Z -> (0 <= j < m)%Z -> (0 <= i' < n)%Z -> (0 <= j' < m)%Z ->
  cell (T.[of_Z (i * m + j) <- v]) m i' j' =
  if (Z.eqb i' i && Z.eqb j' j)%bool then v else cell T m i' j'.
Proof.
  intros T n m i j i' j' v HL Hi Hj Hi' Hj'. unfold cell.
  pose proof (alength_bound T) as Bl.
  assert (Hb1 : (0 <= i * m + j < n * m)%Z) by (split; nia).
  assert (Hb2 : (0 <= i' * m + j' < n * m)%Z) by (split; nia).
  assert (Hne : ~ (i' = i /\ j' = j) ->
     T.[of_Z (i * m + j) <- v].[of_Z (i' * m + j')] = T.[of_Z (i' * m + j')]).
  { intros Hn. apply zget_set_other. intro E.
    apply of_Z_inj_small in E; [ | rewrite wB_val; lia | rewrite wB_val; lia].
    apply Hn. apply idx_inj in E; [ | lia | lia]. destruct E; split; congruence. }
  destruct (Z.eqb_spec i' i), (Z.eqb_spec j' j); simpl.
  - subst. apply zget_set_same. rewrite ltb_spec, of_Z_spec, Z.mod_small; rewrite ?wB_val; lia.
  - apply Hne. tauto.
  - apply Hne. tauto.
  - apply Hne. tauto.
Qed.

(* ------------------------------------------------------------------ *)
(* Math side: sums over Q, solutions of a Z-indexed matrix             *)
(* ------------------------------------------------------------------ *)

Open Scope Z_scope.

Fixpoint sumq (t : Z -> Q) (L : nat) : Q :=
  match L with
  | O => 0%Q
  | S L' => (t 0%Z + sumq (fun x => t (x + 1)%Z) L')%Q
  end.

Lemma sumq_ext : forall L (t t' : Z -> Q),
  (forall x, 0 <= x < Z.of_nat L -> (t x == t' x)%Q) -> (sumq t L == sumq t' L)%Q.
Proof.
  induction L as [| L IH]; intros t t' H; simpl; [reflexivity|].
  apply Qplus_comp; [apply H; lia|]. apply IH. intros x Hx. apply H. lia.
Qed.

Lemma sumq_zero : forall L (t : Z -> Q),
  (forall x, 0 <= x < Z.of_nat L -> (t x == 0)%Q) -> (sumq t L == 0)%Q.
Proof.
  induction L as [| L IH]; intros t H; simpl; [reflexivity|].
  transitivity (0 + 0)%Q; [|reflexivity].
  apply Qplus_comp; [apply H; lia|]. apply IH. intros x Hx. apply H. lia.
Qed.

Lemma sumq_point : forall L (t : Z -> Q) a, 0 <= a < Z.of_nat L ->
  (forall x, 0 <= x < Z.of_nat L -> x <> a -> (t x == 0)%Q) -> (sumq t L == t a)%Q.
Proof.
  induction L as [| L IH]; intros t a Ha H; simpl; [lia|].
  destruct (Z.eq_dec a 0) as [E | E].
  - subst a. transitivity (t 0%Z + 0)%Q; [|ring].
    apply Qplus_comp; [reflexivity|]. apply sumq_zero. intros x Hx. apply H; lia.
  - transitivity (0 + t a)%Q; [|ring].
    apply Qplus_comp; [apply H; lia|].
    rewrite (IH _ (a - 1)); [ | lia | intros x Hx Hxa; apply H; lia].
    replace (a - 1 + 1) with a by lia. reflexivity.
Qed.

Lemma sumq_two : forall L (t : Z -> Q) a b,
  0 <= a < Z.of_nat L -> 0 <= b < Z.of_nat L -> a <> b ->
  (forall x, 0 <= x < Z.of_nat L -> x <> a -> x <> b -> (t x == 0)%Q) ->
  (sumq t L == t a + t b)%Q.
Proof.
  induction L as [| L IH]; intros t a b Ha Hb Hab H; simpl; [lia|].
  destruct (Z.eq_dec a 0) as [E | E]; [|destruct (Z.eq_dec b 0) as [F | F]].
  - subst a. apply Qplus_comp; [reflexivity|].
    rewrite (sumq_point _ _ (b - 1)); [ | lia | intros x Hx Hxb; apply H; lia].
    replace (b - 1 + 1) with b by lia. reflexivity.
  - subst b. transitivity (t 0%Z + t a)%Q; [|ring].
    apply Qplus_comp; [reflexivity|].
    rewrite (sumq_point _ _ (a - 1)); [ | lia | intros x Hx Hxb; apply H; lia].
    replace (a - 1 + 1) with a by lia. reflexivity.
  - transitivity (0 + (t a + t b))%Q; [|ring].
    apply Qplus_comp; [apply H; lia|].
    rewrite (IH _ (a - 1) (b - 1)); [ | lia | lia | lia | intros x Hx Hxa Hxb; apply H; lia].
    replace (a - 1 + 1) with a by lia. replace (b - 1 + 1) with b by lia. reflexivity.
Qed.

Lemma sumq_lin : forall L (t1 t2 t3 : Z -> Q) (g p f : Q),
  (forall x, 0 <= x < Z.of_nat L -> (g * t1 x == p * t2 x - f * t3 x)%Q) ->
  (g * sumq t1 L == p * sumq t2 L - f * sumq t3 L)%Q.
Proof.
  induction L as [| L IH]; intros t1 t2 t3 g p f H; simpl; [ring|].
  pose proof (H 0 ltac:(lia)) as H0.
  pose proof (IH (fun x => t1 (x + 1)) (fun x => t2 (x + 1)) (fun x => t3 (x + 1)) g p f
                 ltac:(intros x Hx; apply H; lia)) as H1.
  rewrite Qmult_plus_distr_r, H0, H1. ring.
Qed.

Lemma injZ_sub : forall x y, (inject_Z (x - y) == inject_Z x - inject_Z y)%Q.
Proof. intros x y. unfold Qeq, Qminus, Qplus, Qopp, inject_Z. simpl. lia. Qed.

Lemma injZ_lin : forall g a p b f c, g * a = p * b - f * c ->
  (inject_Z g * inject_Z a == inject_Z p * inject_Z b - inject_Z f * inject_Z c)%Q.
Proof.
  intros g a p b f c H. rewrite <- !inject_Z_mult, <- injZ_sub, H. reflexivity.
Qed.

Lemma injZ_nz : forall a, a <> 0 -> ~ (inject_Z a == 0)%Q.
Proof. intros a Ha E. apply Ha. apply (inject_Z_injective a 0). exact E. Qed.

Definition rowsum (r : Z -> Z) (d : Z -> Q) (L : nat) : Q :=
  sumq (fun x => inject_Z (r x) * d x)%Q L.

Lemma rowsum_rel : forall L (r' r s : Z -> Z) (d : Z -> Q) (g p f : Z),
  (forall x, 0 <= x < Z.of_nat L -> g * r' x = p * r x - f * s x) ->
  (inject_Z g * rowsum r' d L == inject_Z p * rowsum r d L - inject_Z f * rowsum s d L)%Q.
Proof.
  intros L r' r s d g p f H. unfold rowsum. apply sumq_lin.
  intros x Hx. pose proof (injZ_lin _ _ _ _ _ _ (H x Hx)) as E.
  setoid_replace (inject_Z g * (inject_Z (r' x) * d x))%Q
    with ((inject_Z g * inject_Z (r' x)) * d x)%Q
    using relation Qeq by ring.
  rewrite E. ring.
Qed.

Lemma rowsum_ext : forall L (r r' : Z -> Z) (d : Z -> Q),
  (forall x, 0 <= x < Z.of_nat L -> r x = r' x) -> (rowsum r d L == rowsum r' d L)%Q.
Proof.
  intros L r r' d H. unfold rowsum. apply sumq_ext. intros x Hx. rewrite H by exact Hx. reflexivity.
Qed.

(* d solves the n x m system A *)
Definition sol (A : Z -> Z -> Z) (n m : Z) (d : Z -> Q) : Prop :=
  forall i, 0 <= i < n -> (rowsum (A i) d (Z.to_nat m) == 0)%Q.

(* ------------------------------------------------------------------ *)
(* Math side: the elimination invariant                                *)
(* ------------------------------------------------------------------ *)

(* rows marked used are pivot rows, pivot column piv i < c, alone nonzero
   in their column; the other rows are zero on columns < c *)
Definition PivOK (A : Z -> Z -> Z) (used : Z -> bool) (piv : Z -> Z) (n c : Z) : Prop :=
  (forall i, 0 <= i < n -> used i = true ->
     0 <= piv i < c /\ A i (piv i) <> 0 /\
     forall i', 0 <= i' < n -> i' <> i -> A i' (piv i) = 0) /\
  (forall i, 0 <= i < n -> used i = false -> forall k, 0 <= k < c -> A i k = 0).

Record Inv (A0 A : Z -> Z -> Z) (used : Z -> bool) (n m c : Z) : Prop := {
  inv_sol : forall d, sol A n m d <-> sol A0 n m d;
  inv_piv : exists piv, PivOK A used piv n c
}.

Lemma inv_skip : forall A0 A used n m c,
  Inv A0 A used n m c ->
  (forall i, 0 <= i < n -> used i = true \/ A i c = 0) ->
  Inv A0 A used n m (c + 1).
Proof.
  intros A0 A used n m c [Hs [piv [P1 P2]]] Hc. split; [exact Hs|].
  exists piv. split.
  - intros i Hi Hu. destruct (P1 i Hi Hu) as (Hp & Hnz & Ho). split; [lia|]. split; assumption.
  - intros i Hi Hu k Hk. destruct (Z.eq_dec k c) as [E | E].
    + subst k. destruct (Hc i Hi) as [F | F]; [congruence | exact F].
    + apply (P2 i Hi Hu). lia.
Qed.

Lemma mul_nz : forall a b : Z, a <> 0 -> b <> 0 -> a * b <> 0.
Proof. intros a b Ha Hb E. apply Z.mul_eq_0 in E. tauto. Qed.

Lemma inv_elim : forall A0 A A' used n m c s,
  Inv A0 A used n m c -> 0 <= c < m -> 0 <= s < n -> used s = false -> A s c <> 0 ->
  (forall x, 0 <= x < m -> A' s x = A s x) ->
  (forall i, 0 <= i < n -> i <> s -> exists g f, g <> 0 /\
     (forall x, 0 <= x < m -> g * A' i x = A s c * A i x - f * A s x) /\ A' i c = 0) ->
  Inv A0 A' (fun i => if Z.eqb i s then true else used i) n m (c + 1).
Proof.
  intros A0 A A' used n m c s [Hs [piv [P1 P2]]] Hc Hsn Hus Hp Hrs Hrel.
  split.
  - intros d. rewrite <- Hs. unfold sol. split; intros H i Hi.
    + (* sol A' -> sol A *)
      assert (Es : (rowsum (A s) d (Z.to_nat m) == 0)%Q).
      { rewrite <- (H s Hsn). apply rowsum_ext. intros x Hx. symmetry. apply Hrs. lia. }
      destruct (Z.eq_dec i s) as [E | E]; [subst; exact Es|].
      destruct (Hrel i Hi E) as (g & f & Hg & Hr & _).
      pose proof (rowsum_rel (Z.to_nat m) (A' i) (A i) (A s) d g (A s c) f
                    ltac:(intros x Hx; apply Hr; lia)) as R.
      rewrite (H i Hi), Es in R.
      apply (Qmult_integral_l (inject_Z (A s c))); [apply injZ_nz; exact Hp|].
      rewrite <- (Qplus_0_r (inject_Z (A s c) * _)).
      setoid_replace (inject_Z (A s c) * rowsum (A i) d (Z.to_nat m) + 0)%Q
        with (inject_Z (A s c) * rowsum (A i) d (Z.to_nat m) - inject_Z f * 0)%Q
        using relation Qeq by ring.
      rewrite <- R. ring.
    + (* sol A -> sol A' *)
      destruct (Z.eq_dec i s) as [E | E].
      * subst. rewrite <- (H s Hsn). apply rowsum_ext. intros x Hx. apply Hrs. lia.
      * destruct (Hrel i Hi E) as (g & f & Hg & Hr & _).
        pose proof (rowsum_rel (Z.to_nat m) (A' i) (A i) (A s) d g (A s c) f
                      ltac:(intros x Hx; apply Hr; lia)) as R.
        rewrite (H i Hi), (H s Hsn) in R.
        apply (Qmult_integral_l (inject_Z g)); [apply injZ_nz; exact Hg|].
        rewrite R. ring.
  - exists (fun i => if Z.eqb i s then c else piv i). split.
    + intros i Hi Hu. destruct (Z.eqb_spec i s) as [E | E].
      * subst i. split; [lia|]. split; [rewrite Hrs by lia; exact Hp|].
        intros i' Hi' Hne. destruct (Hrel i' Hi' Hne) as (_ & _ & _ & _ & Z0). exact Z0.
      * destruct (P1 i Hi Hu) as (Hpv & Hnz & Ho).
        assert (Hspi : A s (piv i) = 0) by (apply (P2 s Hsn Hus); lia).
        split; [lia|]. split.
        -- destruct (Hrel i Hi E) as (g & f & Hg & Hr & _).
           pose proof (Hr (piv i) ltac:(lia)) as Q. rewrite Hspi in Q.
           intro Z0. rewrite Z0, Z.mul_0_r in Q.
           apply (mul_nz (A s c) (A i (piv i)) Hp Hnz). lia.
        -- intros i' Hi' Hne. destruct (Z.eq_dec i' s) as [E' | E'].
           ++ subst i'. rewrite Hrs by lia. exact Hspi.
           ++ destruct (Hrel i' Hi' E') as (g & f & Hg & Hr & _).
              pose proof (Hr (piv i) ltac:(lia)) as Q.
              rewrite Hspi, (Ho i' Hi' Hne) in Q.
              rewrite Z.mul_0_r, Z.mul_0_r, Z.sub_0_r in Q.
              apply Z.mul_eq_0 in Q. lia.
    + intros i Hi Hu k Hk. destruct (Z.eqb_spec i s) as [E | E]; [discriminate|].
      destruct (Hrel i Hi E) as (g & f & Hg & Hr & Hc0).
      destruct (Z.eq_dec k c) as [Ek | Ek]; [subst; exact Hc0|].
      pose proof (Hr k ltac:(lia)) as Q.
      rewrite (P2 i Hi Hu k ltac:(lia)), (P2 s Hsn Hus k ltac:(lia)) in Q.
      rewrite Z.mul_0_r, Z.mul_0_r, Z.sub_0_r in Q.
      apply Z.mul_eq_0 in Q. lia.
Qed.

(* ------------------------------------------------------------------ *)
(* Math side: reading the answer off the reduced table                 *)
(* ------------------------------------------------------------------ *)

(* number of nonzero entries among r 0 .. r (L - 1) *)
Fixpoint cnt (r : Z -> Z) (L : nat) : nat :=
  match L with
  | O => O
  | S L' => (cnt r L' + (if Z.eqb (r (Z.of_nat L')) 0 then 0 else 1))%nat
  end.

Lemma cnt_zero : forall r L, cnt r L = O -> forall x, 0 <= x < Z.of_nat L -> r x = 0.
Proof.
  intros r L. induction L as [| L IH]; intros H x Hx; simpl in *; [lia|].
  destruct (Z.eqb_spec (r (Z.of_nat L)) 0) as [E | E]; [|lia].
  destruct (Z.eq_dec x (Z.of_nat L)) as [F | F]; [subst; exact E|].
  apply IH; lia.
Qed.

Lemma cnt_allzero : forall r L, (forall x, 0 <= x < Z.of_nat L -> r x = 0) -> cnt r L = O.
Proof.
  intros r L. induction L as [| L IH]; intros H; simpl; [reflexivity|].
  rewrite IH by (intros x Hx; apply H; lia). rewrite H by lia. reflexivity.
Qed.

Lemma cnt_one : forall r L, cnt r L = 1%nat ->
  exists j, 0 <= j < Z.of_nat L /\ r j <> 0 /\
            forall x, 0 <= x < Z.of_nat L -> x <> j -> r x = 0.
Proof.
  intros r L. induction L as [| L IH]; intros H; simpl in *; [lia|].
  destruct (Z.eqb_spec (r (Z.of_nat L)) 0) as [E | E].
  - destruct (IH ltac:(lia)) as (j & Hj & Hnz & Ho). exists j.
    split; [lia|]. split; [exact Hnz|].
    intros x Hx Hxj. destruct (Z.eq_dec x (Z.of_nat L)) as [F | F]; [subst; exact E|].
    apply Ho; lia.
  - exists (Z.of_nat L). split; [lia|]. split; [exact E|].
    intros x Hx Hxj. apply (cnt_zero r L); lia.
Qed.

Lemma cnt_unique : forall r L j, 0 <= j < Z.of_nat L -> r j <> 0 ->
  (forall x, 0 <= x < Z.of_nat L -> x <> j -> r x = 0) -> cnt r L = 1%nat.
Proof.
  intros r L. induction L as [| L IH]; intros j Hj Hnz H; simpl; [lia|].
  destruct (Z.eq_dec j (Z.of_nat L)) as [E | E].
  - subst j. rewrite cnt_allzero by (intros x Hx; apply H; lia).
    destruct (Z.eqb_spec (r (Z.of_nat L)) 0); [contradiction | reflexivity].
  - rewrite (IH j) by (try lia; try exact Hnz; intros x Hx Hxj; apply H; lia).
    rewrite (H (Z.of_nat L)) by lia. reflexivity.
Qed.

Lemma fin_dec : forall (P : Z -> Prop), (forall x, P x \/ ~ P x) -> forall L,
  (exists x, 0 <= x < Z.of_nat L /\ P x) \/ (forall x, 0 <= x < Z.of_nat L -> ~ P x).
Proof.
  intros P HP L. induction L as [| L IH].
  - right. intros x Hx. simpl in Hx. lia.
  - destruct IH as [(x & Hx & Px) | H].
    + left. exists x. split; [lia | exact Px].
    + destruct (HP (Z.of_nat L)) as [E | E].
      * left. exists (Z.of_nat L). split; [lia | exact E].
      * right. intros x Hx. destruct (Z.eq_dec x (Z.of_nat L)) as [F | F]; [subst; exact E|].
        apply H. lia.
Qed.

Lemma cnt_other : forall r L j, 0 <= j < Z.of_nat L -> r j <> 0 -> cnt r L <> 1%nat ->
  exists k, 0 <= k < Z.of_nat L /\ k <> j /\ r k <> 0.
Proof.
  intros r L j Hj Hnz Hc.
  destruct (fin_dec (fun k => k <> j /\ r k <> 0)
              ltac:(intros x; destruct (Z.eq_dec x j), (Z.eq_dec (r x) 0); tauto) L)
    as [(k & Hk & Pk) | H].
  - exists k. tauto.
  - exfalso. apply Hc. apply (cnt_unique r L j Hj Hnz).
    intros x Hx Hxj. destruct (Z.eq_dec (r x) 0) as [E | E]; [exact E|].
    exfalso. apply (H x Hx). tauto.
Qed.

(* the used row whose pivot column is x, if any *)
Fixpoint findrow (used : Z -> bool) (piv : Z -> Z) (x : Z) (L : nat) : option Z :=
  match L with
  | O => None
  | S L' => if (used (Z.of_nat L') && Z.eqb (piv (Z.of_nat L')) x)%bool
            then Some (Z.of_nat L') else findrow used piv x L'
  end.

Lemma findrow_some : forall used piv x L i, findrow used piv x L = Some i ->
  0 <= i < Z.of_nat L /\ used i = true /\ piv i = x.
Proof.
  intros used piv x L. induction L as [| L IH]; intros i H; simpl in H; [discriminate|].
  destruct (used (Z.of_nat L)) eqn:U, (Z.eqb_spec (piv (Z.of_nat L)) x) as [E | E];
    simpl in H;
    try (destruct (IH i H) as (A & B & C); split; [lia | tauto]).
  injection H as <-. split; [lia|]. tauto.
Qed.

Lemma findrow_none : forall used piv x L, findrow used piv x L = None ->
  forall i, 0 <= i < Z.of_nat L -> used i = true -> piv i <> x.
Proof.
  intros used piv x L. induction L as [| L IH]; intros H i Hi Hu; simpl in *; [lia|].
  destruct (used (Z.of_nat L)) eqn:U, (Z.eqb_spec (piv (Z.of_nat L)) x) as [E | E];
    simpl in H; try discriminate;
    (destruct (Z.eq_dec i (Z.of_nat L)) as [F | F];
     [subst i; congruence | apply (IH H); [lia | exact Hu]]).
Qed.

Lemma piv_unique : forall A used piv n c, PivOK A used piv n c ->
  forall i i', 0 <= i < n -> 0 <= i' < n -> used i = true -> used i' = true ->
  piv i = piv i' -> i = i'.
Proof.
  intros A used piv n c [P1 _] i i' Hi Hi' Hu Hu' E.
  destruct (Z.eq_dec i i') as [F | F]; [exact F|].
  destruct (P1 i Hi Hu) as (_ & _ & Ho). destruct (P1 i' Hi' Hu') as (_ & Hnz & _).
  exfalso. apply Hnz. rewrite <- E. apply Ho; [exact Hi' | auto].
Qed.

(* the solution with free column k set to 1 *)
Definition dk (A : Z -> Z -> Z) (used : Z -> bool) (piv : Z -> Z) (n k : Z) (x : Z) : Q :=
  if Z.eqb x k then 1%Q
  else match findrow used piv x (Z.to_nat n) with
       | Some i => (- inject_Z (A i k) / inject_Z (A i x))%Q
       | None => 0%Q
       end.

Lemma dk_piv : forall A used piv n m k, PivOK A used piv n m ->
  (forall i, 0 <= i < n -> used i = true -> piv i <> k) ->
  forall i, 0 <= i < n -> used i = true ->
  (dk A used piv n k (piv i) == - inject_Z (A i k) / inject_Z (A i (piv i)))%Q.
Proof.
  intros A used piv n m k HP Hk i Hi Hu. unfold dk.
  destruct (Z.eqb_spec (piv i) k) as [E | E]; [exfalso; exact (Hk i Hi Hu E)|].
  destruct (findrow used piv (piv i) (Z.to_nat n)) as [i' |] eqn:F.
  - destruct (findrow_some _ _ _ _ _ F) as (Hi' & Hu' & Hp').
    assert (i' = i) by (apply (piv_unique A used piv n m HP); try lia; assumption).
    subst i'. reflexivity.
  - exfalso. apply (findrow_none _ _ _ _ F i ltac:(lia) Hu). reflexivity.
Qed.

Lemma build_sol : forall A used piv n m k, 0 <= n -> PivOK A used piv n m ->
  0 <= k < m -> (forall i, 0 <= i < n -> used i = true -> piv i <> k) ->
  sol A n m (dk A used piv n k).
Proof.
  intros A used piv n m k Hn HP Hk Hnp. pose proof HP as [P1 P2].
  intros i Hi. unfold rowsum.
  destruct (used i) eqn:Hu.
  - destruct (P1 i Hi Hu) as (Hpv & Hnz & Ho).
    rewrite (sumq_two _ _ k (piv i)); [ | lia | lia | apply not_eq_sym; apply Hnp; assumption | ].
    + rewrite (dk_piv A used piv n m k HP Hnp i Hi Hu).
      unfold dk at 1. rewrite Z.eqb_refl.
      field. apply injZ_nz. exact Hnz.
    + intros x Hx Hxk Hxp. unfold dk.
      destruct (Z.eqb_spec x k) as [E | E]; [contradiction|].
      destruct (findrow used piv x (Z.to_nat n)) as [i' |] eqn:F.
      * destruct (findrow_some _ _ _ _ _ F) as (Hi' & Hu' & Hp').
        assert (Hii : i <> i') by (intro Q; subst i'; apply Hxp; symmetry; exact Hp').
        destruct (P1 i' ltac:(lia) Hu') as (_ & _ & Ho').
        rewrite <- Hp', (Ho' i Hi Hii). ring.
      * ring.
  - apply sumq_zero. intros x Hx. rewrite (P2 i Hi Hu x ltac:(lia)). ring.
Qed.

Lemma final_iff : forall A0 A used piv n m, 0 <= n -> 0 <= m ->
  PivOK A used piv n m -> (forall d, sol A n m d <-> sol A0 n m d) ->
  ((forall i, 0 <= i < n -> cnt (A i) (Z.to_nat m) <> 1%nat) <->
   (forall j, 0 <= j < m -> exists d, sol A0 n m d /\ ~ (d j == 0)%Q)).
Proof.
  intros A0 A used piv n m Hn Hm HP Hs. pose proof HP as [P1 P2]. split.
  - intros Hc j Hj.
    destruct (fin_dec (fun i => used i = true /\ piv i = j)
                ltac:(intros x; cbv beta; destruct (Bool.bool_dec (used x) true), (Z.eq_dec (piv x) j); tauto)
                (Z.to_nat n)) as [(i & Hi & Hu & Hpj) | Hno].
    + destruct (P1 i ltac:(lia) Hu) as (Hpv & Hnz & Ho).
      destruct (cnt_other (A i) (Z.to_nat m) j ltac:(lia) ltac:(rewrite <- Hpj; exact Hnz)
                  (Hc i ltac:(lia))) as (k & Hk & Hkj & Hak).
      assert (Hnp : forall i', 0 <= i' < n -> used i' = true -> piv i' <> k).
      { intros i' Hi' Hu' E. destruct (Z.eq_dec i' i) as [F | F].
        - subst i'. lia.
        - destruct (P1 i' Hi' Hu') as (_ & _ & Ho'). apply Hak. rewrite <- E.
          apply Ho'; [lia | auto]. }
      exists (dk A used piv n k). split.
      * apply Hs. apply build_sol; [lia | exact HP | lia | exact Hnp].
      * rewrite <- Hpj, (dk_piv A used piv n m k HP Hnp i ltac:(lia) Hu).
        intro Z0. apply (injZ_nz _ Hak).
        setoid_replace (inject_Z (A i k))
          with (- (- inject_Z (A i k) / inject_Z (A i (piv i))) * inject_Z (A i (piv i)))%Q
          using relation Qeq by (field; apply injZ_nz; exact Hnz).
        rewrite Z0. ring.
    + exists (dk A used piv n j). split.
      * apply Hs. apply build_sol; [lia | exact HP | lia |].
        intros i Hi Hu E. apply (Hno i ltac:(lia)). tauto.
      * unfold dk. rewrite Z.eqb_refl. discriminate.
  - intros Hf i Hi Hc.
    destruct (cnt_one (A i) (Z.to_nat m) Hc) as (j & Hj & Hnz & Ho).
    destruct (Hf j ltac:(lia)) as (d & Hd & Hdj).
    apply Hs in Hd. pose proof (Hd i Hi) as R. unfold rowsum in R.
    rewrite (sumq_point _ _ j Hj) in R.
    + apply Qmult_integral in R. destruct R as [R | R]; [exact (injZ_nz _ Hnz R) | exact (Hdj R)].
    + intros x Hx Hxj. rewrite (Ho x Hx Hxj). ring.
Qed.

(* ------------------------------------------------------------------ *)
(* The loops of the program, one spec each                             *)
(* ------------------------------------------------------------------ *)

Ltac for_inv Q :=
  match goal with |- context [for_ ?lo ?hi ?s ?f] =>
    assert (Hfor : Q (φ hi) (for_ lo hi s f)); [apply (for_spec Q) | ]
  end.

Lemma bnd : forall n m i j : Z, n * m <= 4194303 -> 0 <= i < n -> 0 <= j < m ->
  0 <= i * m + j < 4194304 /\ i * m + j < n * m.
Proof. intros n m i j H Hi Hj. split; [split|]; nia. Qed.

Lemma phi_of_Z : forall z, 0 <= z < wB -> (φ (of_Z z)) = z.
Proof. intros z Hz. rewrite of_Z_spec. apply Z.mod_small. exact Hz. Qed.

Lemma ztab_spec : forall (n m : int) (xe : array (array sint)),
  (φ n) * (φ m) <= 4194303 ->
  (φ (PArray.length (ztab n m xe))) = (φ n) * (φ m) /\
  forall i j, 0 <= i < (φ n) -> 0 <= j < (φ m) ->
    cell (ztab n m xe) (φ m) i j = Sint63.to_Z ((xe.[of_Z i]).[of_Z j]).
Proof.
  intros n m xe Hnm.
  pose proof (to_Z_bounded n) as Bn. pose proof (to_Z_bounded m) as Bm.
  assert (Hm0 : (φ (PArray.length (PArray.make (n * m) 0%Z))) = (φ n) * (φ m)).
  { rewrite length_make.
    assert (E : (φ (n * m))%uint63 = (φ n) * (φ m)) by (rewrite mul_spec; apply Z.mod_small; rewrite wB_val; nia).
    replace (n * m <=? max_length)%uint63 with true; [exact E|].
    symmetry. rewrite leb_spec, max_length_val. lia. }
  unfold ztab.
  apply (for_spec (fun z T => (φ (PArray.length T)) = (φ n) * (φ m) /\
           forall i j, 0 <= i < z -> 0 <= j < (φ m) ->
             cell T (φ m) i j = Sint63.to_Z ((xe.[of_Z i]).[of_Z j]))).
  - change (φ 0) with 0. lia.
  - split; [exact Hm0|]. intros i j Hi. change (φ 0) with 0 in Hi. lia.
  - intros i T Hi [HL HT]. change (φ 0) with 0 in Hi. cbv beta zeta.
    for_inv (fun z T' => (φ (PArray.length T')) = (φ n) * (φ m) /\
           forall i' j, 0 <= i' < (φ i) + 1 -> 0 <= j < (φ m) -> (i' < (φ i) \/ j < z) ->
             cell T' (φ m) i' j = Sint63.to_Z ((xe.[of_Z i']).[of_Z j])).
    + change (φ 0) with 0. lia.
    + split; [exact HL|]. intros i' j Hi' Hj [Hlt | Hlt]; [apply HT; lia | lia].
    + intros j T' Hj [HL' HT']. change (φ 0) with 0 in Hj. cbv beta.
      destruct (bnd (φ n) (φ m) (φ i) (φ j) Hnm ltac:(lia) ltac:(lia)) as [B1 B2].
      rewrite set_idx by exact B1. split; [rewrite zlength_set; exact HL'|].
      intros i' j' Hi' Hj' Hor.
      rewrite (cell_set _ (φ n) (φ m)) by (try exact HL'; lia).
      destruct (Z.eqb_spec i' (φ i)), (Z.eqb_spec j' (φ j)); simpl.
      * subst. rewrite !of_to_Z. apply sconv_spec.
      * apply HT'; [lia | lia | lia].
      * apply HT'; [lia | lia | lia].
      * apply HT'; [lia | lia | lia].
    + destruct Hfor as [HL' HT']. split; [exact HL'|].
      intros i' j Hi' Hj. apply HT'; [lia | lia | lia].
Qed.

Section Rows.
  Variables (n m : int).
  Hypothesis Hnm : (φ n) * (φ m) <= 4194303.

  Lemma upd_row_spec : forall (i s : int) (p f : Z) (T : array Z),
    (φ (PArray.length T)) = (φ n) * (φ m) -> 0 <= (φ i) < (φ n) -> 0 <= (φ s) < (φ n) -> (φ i) <> (φ s) ->
    (φ (PArray.length (upd_row m i s p f T))) = (φ n) * (φ m) /\
    forall i' x, 0 <= i' < (φ n) -> 0 <= x < (φ m) ->
      cell (upd_row m i s p f T) (φ m) i' x =
      if Z.eqb i' (φ i) then p * cell T (φ m) (φ i) x - f * cell T (φ m) (φ s) x
      else cell T (φ m) i' x.
  Proof.
    intros i s p f T HL Hi Hs His. unfold upd_row.
    for_inv (fun z T' => (φ (PArray.length T')) = (φ n) * (φ m) /\
      forall i' x, 0 <= i' < (φ n) -> 0 <= x < (φ m) ->
      cell T' (φ m) i' x =
      if (Z.eqb i' (φ i) && Z.ltb x z)%bool
      then p * cell T (φ m) (φ i) x - f * cell T (φ m) (φ s) x
      else cell T (φ m) i' x).
    - change (φ 0) with 0. pose proof (to_Z_bounded m). lia.
    - split; [exact HL|]. intros i' x Hi' Hx. change (φ 0) with 0.
      replace (Z.ltb x 0) with false by (symmetry; apply Z.ltb_ge; lia).
      rewrite Bool.andb_false_r. reflexivity.
    - intros j T' Hj [HL' HT']. change (φ 0) with 0 in Hj. cbv beta.
      destruct (bnd (φ n) (φ m) (φ i) (φ j) Hnm ltac:(lia) ltac:(lia)) as [B1 B2].
      destruct (bnd (φ n) (φ m) (φ s) (φ j) Hnm ltac:(lia) ltac:(lia)) as [B3 B4].
      rewrite set_idx by exact B1. rewrite !get_idx by assumption.
      rewrite (HT' (φ i) (φ j)) by lia. rewrite (HT' (φ s) (φ j)) by lia.
      rewrite Z.eqb_refl, Z.ltb_irrefl.
      replace (Z.eqb (φ s) (φ i)) with false by (symmetry; apply Z.eqb_neq; lia).
      simpl. split; [rewrite zlength_set; exact HL'|].
      intros i' x Hi' Hx.
      rewrite (cell_set _ (φ n) (φ m)) by (try exact HL'; lia).
      rewrite HT' by lia.
      destruct (Z.eqb_spec i' (φ i)), (Z.eqb_spec x (φ j)),
               (Z.ltb_spec x (φ j)), (Z.ltb_spec x ((φ j) + 1)); simpl;
        subst; try reflexivity; lia.
    - destruct Hfor as [HL' HT']. split; [exact HL'|].
      intros i' x Hi' Hx. rewrite HT' by assumption.
      replace (Z.ltb x (φ m)) with true by (symmetry; apply Z.ltb_lt; lia).
      rewrite Bool.andb_true_r. reflexivity.
  Qed.

  Lemma div_row_spec : forall (i : int) (g : Z) (T : array Z),
    (φ (PArray.length T)) = (φ n) * (φ m) -> 0 <= (φ i) < (φ n) ->
    (φ (PArray.length (div_row m i g T))) = (φ n) * (φ m) /\
    forall i' x, 0 <= i' < (φ n) -> 0 <= x < (φ m) ->
      cell (div_row m i g T) (φ m) i' x =
      if Z.eqb i' (φ i) then cell T (φ m) (φ i) x / g else cell T (φ m) i' x.
  Proof.
    intros i g T HL Hi. unfold div_row.
    for_inv (fun z T' => (φ (PArray.length T')) = (φ n) * (φ m) /\
      forall i' x, 0 <= i' < (φ n) -> 0 <= x < (φ m) ->
      cell T' (φ m) i' x =
      if (Z.eqb i' (φ i) && Z.ltb x z)%bool
      then cell T (φ m) (φ i) x / g
      else cell T (φ m) i' x).
    - change (φ 0) with 0. pose proof (to_Z_bounded m). lia.
    - split; [exact HL|]. intros i' x Hi' Hx. change (φ 0) with 0.
      replace (Z.ltb x 0) with false by (symmetry; apply Z.ltb_ge; lia).
      rewrite Bool.andb_false_r. reflexivity.
    - intros j T' Hj [HL' HT']. change (φ 0) with 0 in Hj. cbv beta.
      destruct (bnd (φ n) (φ m) (φ i) (φ j) Hnm ltac:(lia) ltac:(lia)) as [B1 B2].
      rewrite set_idx by exact B1. rewrite !get_idx by assumption.
      rewrite (HT' (φ i) (φ j)) by lia.
      rewrite Z.eqb_refl, Z.ltb_irrefl.
      simpl. split; [rewrite zlength_set; exact HL'|].
      intros i' x Hi' Hx.
      rewrite (cell_set _ (φ n) (φ m)) by (try exact HL'; lia).
      rewrite HT' by lia.
      destruct (Z.eqb_spec i' (φ i)), (Z.eqb_spec x (φ j)),
               (Z.ltb_spec x (φ j)), (Z.ltb_spec x ((φ j) + 1)); simpl;
        subst; try reflexivity; lia.
    - destruct Hfor as [HL' HT']. split; [exact HL'|].
      intros i' x Hi' Hx. rewrite HT' by assumption.
      replace (Z.ltb x (φ m)) with true by (symmetry; apply Z.ltb_lt; lia).
      rewrite Bool.andb_true_r. reflexivity.
  Qed.

  Lemma row_gcd_spec : forall (i : int) (T : array Z), 0 <= (φ i) < (φ n) ->
    forall x, 0 <= x < (φ m) -> (row_gcd m i T | cell T (φ m) (φ i) x).
  Proof.
    intros i T Hi. unfold row_gcd.
    for_inv (fun z g => forall x, 0 <= x < z -> (g | cell T (φ m) (φ i) x)).
    - change (φ 0) with 0. pose proof (to_Z_bounded m). lia.
    - intros x Hx. change (φ 0) with 0 in Hx. lia.
    - intros j g Hj Hg x Hx. change (φ 0) with 0 in Hj. cbv beta.
      destruct (bnd (φ n) (φ m) (φ i) (φ j) Hnm ltac:(lia) ltac:(lia)) as [B1 B2].
      rewrite zgcd_spec, get_idx by exact B1.
      destruct (Z.eq_dec x (φ j)) as [E | E].
      + subst. apply Z.gcd_divide_r.
      + eapply Z.divide_trans; [apply Z.gcd_divide_l | apply Hg; lia].
    - exact Hfor.
  Qed.

  Lemma norm_row_spec : forall (i : int) (T : array Z),
    (φ (PArray.length T)) = (φ n) * (φ m) -> 0 <= (φ i) < (φ n) ->
    (φ (PArray.length (norm_row m i T))) = (φ n) * (φ m) /\
    exists g, g <> 0 /\
      (forall x, 0 <= x < (φ m) -> g * cell (norm_row m i T) (φ m) (φ i) x = cell T (φ m) (φ i) x) /\
      (forall i' x, 0 <= i' < (φ n) -> 0 <= x < (φ m) -> i' <> (φ i) ->
         cell (norm_row m i T) (φ m) i' x = cell T (φ m) i' x).
  Proof.
    intros i T HL Hi. unfold norm_row.
    destruct (Z.ltb_spec 1 (row_gcd m i T)) as [Hg | Hg].
    - destruct (div_row_spec i (row_gcd m i T) T HL Hi) as [HL' HT'].
      split; [exact HL'|]. exists (row_gcd m i T). split; [lia|]. split.
      + intros x Hx. rewrite HT' by lia. rewrite Z.eqb_refl.
        destruct (row_gcd_spec i T Hi x Hx) as [k Hk]. rewrite Hk, Z.div_mul by lia. ring.
      + intros i' x Hi' Hx Hne. rewrite HT' by lia.
        replace (Z.eqb i' (φ i)) with false by (symmetry; apply Z.eqb_neq; exact Hne).
        reflexivity.
    - split; [exact HL|]. exists 1. split; [lia|]. split.
      + intros x Hx. ring.
      + intros i' x Hi' Hx Hne. reflexivity.
  Qed.

  Lemma row_step_spec : forall (i s : int) (p f : Z) (T : array Z),
    (φ (PArray.length T)) = (φ n) * (φ m) -> 0 <= (φ i) < (φ n) -> 0 <= (φ s) < (φ n) -> (φ i) <> (φ s) ->
    (φ (PArray.length (norm_row m i (upd_row m i s p f T)))) = (φ n) * (φ m) /\
    exists g, g <> 0 /\
      (forall x, 0 <= x < (φ m) ->
         g * cell (norm_row m i (upd_row m i s p f T)) (φ m) (φ i) x
         = p * cell T (φ m) (φ i) x - f * cell T (φ m) (φ s) x) /\
      (forall i' x, 0 <= i' < (φ n) -> 0 <= x < (φ m) -> i' <> (φ i) ->
         cell (norm_row m i (upd_row m i s p f T)) (φ m) i' x = cell T (φ m) i' x).
  Proof.
    intros i s p f T HL Hi Hs His.
    destruct (upd_row_spec i s p f T HL Hi Hs His) as [HL1 HT1].
    destruct (norm_row_spec i _ HL1 Hi) as [HL2 (g & Hg & Hr & Ho)].
    split; [exact HL2|]. exists g. split; [exact Hg|]. split.
    - intros x Hx. rewrite Hr by exact Hx. rewrite HT1 by lia. rewrite Z.eqb_refl. reflexivity.
    - intros i' x Hi' Hx Hne. rewrite Ho by assumption. rewrite HT1 by assumption.
      replace (Z.eqb i' (φ i)) with false by (symmetry; apply Z.eqb_neq; exact Hne).
      reflexivity.
  Qed.

  Lemma elim_rows_spec : forall (s c : int) (T : array Z),
    (φ (PArray.length T)) = (φ n) * (φ m) -> 0 <= (φ s) < (φ n) -> 0 <= (φ c) < (φ m) ->
    cell T (φ m) (φ s) (φ c) <> 0 ->
    (φ (PArray.length (elim_rows n m s c T))) = (φ n) * (φ m) /\
    (forall x, 0 <= x < (φ m) -> cell (elim_rows n m s c T) (φ m) (φ s) x = cell T (φ m) (φ s) x) /\
    (forall i, 0 <= i < (φ n) -> i <> (φ s) -> exists g f, g <> 0 /\
       (forall x, 0 <= x < (φ m) ->
          g * cell (elim_rows n m s c T) (φ m) i x
          = cell T (φ m) (φ s) (φ c) * cell T (φ m) i x - f * cell T (φ m) (φ s) x) /\
       cell (elim_rows n m s c T) (φ m) i (φ c) = 0).
  Proof.
    intros s c T HL Hs Hc Hp. unfold elim_rows.
    destruct (bnd (φ n) (φ m) (φ s) (φ c) Hnm ltac:(lia) ltac:(lia)) as [B1 B2].
    rewrite (get_idx T s m c B1).
    set (p := cell T (φ m) (φ s) (φ c)) in *.
    for_inv (fun z T' => (φ (PArray.length T')) = (φ n) * (φ m) /\
      (forall i x, 0 <= i < (φ n) -> 0 <= x < (φ m) -> (i = (φ s) \/ z <= i) ->
         cell T' (φ m) i x = cell T (φ m) i x) /\
      (forall i, 0 <= i < z -> i <> (φ s) -> exists g f, g <> 0 /\
         (forall x, 0 <= x < (φ m) ->
            g * cell T' (φ m) i x = p * cell T (φ m) i x - f * cell T (φ m) (φ s) x) /\
         cell T' (φ m) i (φ c) = 0)).
    - change (φ 0) with 0. lia.
    - split; [exact HL|]. split; [intros; reflexivity|].
      intros i Hi. change (φ 0) with 0 in Hi. lia.
    - intros i T' Hi [HL' [HU HR]]. change (φ 0) with 0 in Hi. cbv beta zeta.
      destruct (i =? s)%uint63 eqn:Eis.
      + rewrite eqb_spec in Eis. subst i.
        split; [exact HL'|]. split.
        * intros i' x Hi' Hx Hor. apply HU; lia.
        * intros i' Hi' Hne. apply HR; lia.
      + rewrite eqb_false_spec in Eis.
        assert (Eis' : (φ i) <> (φ s)) by (intro E; apply Eis; apply to_Z_inj; exact E).
        destruct (bnd (φ n) (φ m) (φ i) (φ c) Hnm ltac:(lia) ltac:(lia)) as [B3 B4].
        rewrite (get_idx T' i m c B3).
        rewrite (HU (φ i) (φ c)) by lia.
        destruct (Z.eqb_spec (cell T (φ m) (φ i) (φ c)) 0) as [Ef | Ef].
        * split; [exact HL'|]. split.
          -- intros i' x Hi' Hx Hor. apply HU; lia.
          -- intros i' Hi' Hne. destruct (Z.eq_dec i' (φ i)) as [E | E].
             ++ subst i'. exists p, 0. split; [exact Hp|]. split.
                ** intros x Hx. rewrite HU by lia. ring.
                ** rewrite HU by lia. exact Ef.
             ++ apply HR; lia.
        * destruct (row_step_spec i s p (cell T (φ m) (φ i) (φ c)) T' HL' ltac:(lia) Hs Eis')
            as [HL2 (g & Hg & Hr & Ho)].
          split; [exact HL2|]. split.
          -- intros i' x Hi' Hx Hor. rewrite Ho by lia. apply HU; lia.
          -- intros i' Hi' Hne. destruct (Z.eq_dec i' (φ i)) as [E | E].
             ++ subst i'. exists g, (cell T (φ m) (φ i) (φ c)). split; [exact Hg|]. split.
                ** intros x Hx. rewrite Hr by exact Hx. rewrite !HU by lia. reflexivity.
                ** pose proof (Hr (φ c) Hc) as Q. rewrite !HU in Q by lia.
                   fold p in Q.
                   replace (p * cell T (φ m) (φ i) (φ c) - cell T (φ m) (φ i) (φ c) * p)
                     with 0 in Q by ring.
                   apply Z.mul_eq_0 in Q. lia.
             ++ destruct (HR i' ltac:(lia) Hne) as (g0 & f0 & Hg0 & Hr0 & Hc0).
                exists g0, f0. split; [exact Hg0|]. split.
                ** intros x Hx. rewrite Ho by lia. apply Hr0. exact Hx.
                ** rewrite Ho by lia. exact Hc0.
    - destruct Hfor as [HL' [HU HR]]. split; [exact HL'|]. split.
      + intros x Hx. apply HU; lia.
      + intros i Hi Hne. apply HR; lia.
  Qed.

  Lemma find_piv_spec : forall (c : int) (T : array Z) (U : array bool),
    0 <= (φ c) < (φ m) ->
    ((φ (find_piv n m c T U)) = (φ n) /\
       forall i, 0 <= i < (φ n) -> U.[of_Z i] = true \/ cell T (φ m) i (φ c) = 0) \/
    (0 <= (φ (find_piv n m c T U)) < (φ n) /\ U.[find_piv n m c T U] = false /\
       cell T (φ m) (φ (find_piv n m c T U)) (φ c) <> 0).
  Proof.
    intros c T U Hc. unfold find_piv.
    for_inv (fun z r =>
      ((φ r) = (φ n) /\ forall i, 0 <= i < z -> U.[of_Z i] = true \/ cell T (φ m) i (φ c) = 0) \/
      (0 <= (φ r) < z /\ U.[r] = false /\ cell T (φ m) (φ r) (φ c) <> 0)).
    - change (φ 0) with 0. pose proof (to_Z_bounded n). lia.
    - left. split; [reflexivity|]. intros i Hi. change (φ 0) with 0 in Hi. lia.
    - intros i r Hi Hr. change (φ 0) with 0 in Hi. cbv beta.
      destruct (r =? n)%uint63 eqn:Ern.
      + rewrite eqb_spec in Ern. subst r.
        assert (Hl : forall i', 0 <= i' < (φ i) -> U.[of_Z i'] = true \/ cell T (φ m) i' (φ c) = 0)
          by (destruct Hr as [[_ H] | [H _]]; [exact H | lia]).
        destruct (U.[i]) eqn:Ui.
        * left. split; [reflexivity|]. intros i' Hi'.
          destruct (Z.eq_dec i' (φ i)) as [E | E]; [subst; rewrite of_to_Z; left; exact Ui|].
          apply Hl. lia.
        * destruct (bnd (φ n) (φ m) (φ i) (φ c) Hnm ltac:(lia) ltac:(lia)) as [B1 B2].
          rewrite (get_idx T i m c B1).
          destruct (Z.eqb_spec (cell T (φ m) (φ i) (φ c)) 0) as [E0 | E0].
          -- left. split; [reflexivity|]. intros i' Hi'.
             destruct (Z.eq_dec i' (φ i)) as [E | E]; [|apply Hl; lia].
             subst i'. right. exact E0.
          -- right. split; [lia|]. split; assumption.
      + rewrite eqb_false_spec in Ern.
        destruct Hr as [[E _] | (H1 & H2 & H3)]; [exfalso; apply Ern; apply to_Z_inj; exact E|].
        right. split; [lia|]. split; assumption.
    - exact Hfor.
  Qed.

  Lemma col_loop_spec : forall (A0 : Z -> Z -> Z) (T0 : array Z) (U0 : array bool),
    (φ (PArray.length T0)) = (φ n) * (φ m) -> (φ (PArray.length U0)) = (φ n) ->
    Inv A0 (cell T0 (φ m)) (fun i => U0.[of_Z i]) (φ n) (φ m) 0 ->
    (φ (PArray.length (fst (for_ 0 m (T0, U0) (col_step n m))))) = (φ n) * (φ m) /\
    (φ (PArray.length (snd (for_ 0 m (T0, U0) (col_step n m))))) = (φ n) /\
    Inv A0 (cell (fst (for_ 0 m (T0, U0) (col_step n m))) (φ m))
        (fun i => (snd (for_ 0 m (T0, U0) (col_step n m))).[of_Z i]) (φ n) (φ m) (φ m).
  Proof.
    intros A0 T0 U0 HL0 HU0 HI0.
    for_inv (fun z st => (φ (PArray.length (fst st))) = (φ n) * (φ m) /\
      (φ (PArray.length (snd st))) = (φ n) /\
      Inv A0 (cell (fst st) (φ m)) (fun i => (snd st).[of_Z i]) (φ n) (φ m) z).
    - change (φ 0) with 0. pose proof (to_Z_bounded m). lia.
    - split; [exact HL0|]. split; [exact HU0|]. exact HI0.
    - intros c [T U] Hc [HL [HU HI]]. change (φ 0) with 0 in Hc. simpl in HL, HU, HI.
      unfold col_step. simpl fst. simpl snd.
      destruct (find_piv_spec c T U Hc) as [[Er Hall] | (Hr & Hu & Hnz)].
      + replace (find_piv n m c T U =? n)%uint63 with true
          by (symmetry; rewrite eqb_spec; apply to_Z_inj; exact Er).
        simpl. split; [exact HL|]. split; [exact HU|].
        apply inv_skip; [exact HI|]. exact Hall.
      + set (r := find_piv n m c T U) in *.
        replace (r =? n)%uint63 with false
          by (symmetry; rewrite eqb_false_spec; intro E; rewrite E in Hr; lia).
        simpl.
        destruct (elim_rows_spec r c T HL Hr Hc Hnz) as [HL' [Hs' Hrel']].
        split; [exact HL'|]. split; [rewrite blength_set; exact HU|].
        assert (HI' : Inv A0 (cell (elim_rows n m r c T) (φ m))
                  (fun i => if Z.eqb i (φ r) then true else U.[of_Z i]) (φ n) (φ m) ((φ c) + 1)).
        { apply inv_elim with (A := cell T (φ m)); try assumption; try lia.
          rewrite of_to_Z. exact Hu. }
        destruct HI' as [Hsol [piv [P1 P2]]].
        assert (Hus : forall i, 0 <= i < (φ n) ->
                  (U.[r <- true]).[of_Z i] = if Z.eqb i (φ r) then true else U.[of_Z i]).
        { intros i Hi. destruct (Z.eqb_spec i (φ r)) as [E | E].
          - subst i. rewrite of_to_Z. apply bget_set_same. rewrite ltb_spec. lia.
          - apply bget_set_other. intro F. apply E. rewrite F. symmetry. apply phi_of_Z.
            pose proof (to_Z_bounded n). rewrite wB_val. lia. }
        split; [exact Hsol|]. exists piv. split.
        * intros i Hi Hui. rewrite Hus in Hui by exact Hi. apply P1; assumption.
        * intros i Hi Hui. rewrite Hus in Hui by exact Hi. apply P2; assumption.
    - exact Hfor.
  Qed.

  Lemma count_nz_spec : forall (i : int) (T : array Z), 0 <= (φ i) < (φ n) ->
    (φ (count_nz m i T)) = Z.of_nat (cnt (cell T (φ m) (φ i)) (Z.to_nat (φ m))).
  Proof.
    intros i T Hi. unfold count_nz.
    for_inv (fun z k => (φ k) = Z.of_nat (cnt (cell T (φ m) (φ i)) (Z.to_nat z)) /\ (φ k) <= z).
    - change (φ 0) with 0. pose proof (to_Z_bounded m). lia.
    - change (φ 0) with 0. simpl. lia.
    - intros j k Hj [Hk Hkb]. change (φ 0) with 0 in Hj. cbv beta.
      destruct (bnd (φ n) (φ m) (φ i) (φ j) Hnm ltac:(lia) ltac:(lia)) as [B1 B2].
      rewrite (get_idx T i m j B1).
      replace (Z.to_nat ((φ j) + 1)) with (S (Z.to_nat (φ j))) by lia.
      simpl cnt. rewrite Z2Nat.id by lia.
      destruct (Z.eqb_spec (cell T (φ m) (φ i) (φ j)) 0) as [E | E].
      + rewrite Nat.add_0_r. lia.
      + pose proof (to_Z_bounded m).
        assert (E1 : (φ (k + 1)) = (φ k) + 1) by (rewrite add_spec; change (φ 1) with 1;
                                               apply Z.mod_small; rewrite wB_val; lia).
        rewrite E1. lia.
    - destruct Hfor as [Hk _]. exact Hk.
  Qed.

  Lemma final_loop_spec : forall (T : array Z),
    for_ 0 n true (fun i b => if b then negb (count_nz m i T =? 1)%uint63 else false) = true <->
    forall i, 0 <= i < (φ n) -> cnt (cell T (φ m) i) (Z.to_nat (φ m)) <> 1%nat.
  Proof.
    intros T.
    for_inv (fun z (b : bool) => b = true <->
      forall i, 0 <= i < z -> cnt (cell T (φ m) i) (Z.to_nat (φ m)) <> 1%nat).
    - change (φ 0) with 0. pose proof (to_Z_bounded n). lia.
    - split; [intros _ i Hi; change (φ 0) with 0 in Hi; lia | reflexivity].
    - intros i b Hi Hb. change (φ 0) with 0 in Hi. cbv beta.
      destruct b.
      + pose proof (count_nz_spec i T ltac:(lia)) as Ec.
        destruct (count_nz m i T =? 1)%uint63 eqn:E.
        * rewrite eqb_spec in E. rewrite E in Ec. change (φ 1) with 1 in Ec.
          simpl. split; [discriminate|]. intros H. exfalso. apply (H (φ i)); [lia|]. lia.
        * rewrite eqb_false_spec in E. simpl. split; [|reflexivity]. intros _ i' Hi'.
          destruct (Z.eq_dec i' (φ i)) as [F | F].
          -- subst i'. intro C. apply E. apply to_Z_inj. rewrite Ec, C. reflexivity.
          -- apply (proj1 Hb eq_refl). lia.
      + split; [discriminate|]. intros H. apply Hb. intros i' Hi'. apply H. lia.
    - exact Hfor.
  Qed.
End Rows.

(* ------------------------------------------------------------------ *)
(* The bridge to the spec                                              *)
(* ------------------------------------------------------------------ *)

(* the input matrix, Z-indexed *)
Definition Ae (e : list (list Z)) (i j : Z) : Z := nth (Z.to_nat j) (nth (Z.to_nat i) e []) 0.

Lemma repr_cells : forall (e : list (list Z)) (xe : array (array sint)) (m : N),
  repr xe e -> Forall (fun row => len row = m) e ->
  forall i j, 0 <= i < Z.of_nat (List.length e) -> 0 <= j < Z.of_N m ->
  Sint63.to_Z ((xe.[of_Z i]).[of_Z j]) = Ae e i j.
Proof.
  intros e xe m [Hl Hc] HF i j Hi Hj.
  destruct (Hc (Z.to_nat i) ltac:(lia)) as (row & Hrow & Hr).
  destruct Hr as [Hl2 Hc2].
  assert (Hlen : List.length row = N.to_nat m).
  { rewrite Forall_forall in HF. specialize (HF row (nth_error_In _ _ Hrow)).
    unfold len in HF. lia. }
  destruct (Hc2 (Z.to_nat j) ltac:(lia)) as (v & Hv & Hrv).
  assert (E1 : nth (Z.to_nat i) e [] = row) by (apply nth_error_nth; exact Hrow).
  assert (E2 : nth (Z.to_nat j) row 0 = v) by (apply nth_error_nth; exact Hv).
  unfold Ae. rewrite E1, E2.
  cbv [repr repr_sint] in Hrv. rewrite !Z2Nat.id in Hrv by lia. exact Hrv.
Qed.

Lemma row_value_sumq : forall row (d : assignment) j0,
  (row_value row d j0 ==
   sumq (fun x => inject_Z (nth (Z.to_nat x) row 0%Z) * d (j0 + Z.to_N x)%N) (List.length row))%Q.
Proof.
  induction row as [| a row IH]; intros d j0; simpl; [reflexivity|].
  apply Qplus_comp.
  - rewrite N.add_0_r. reflexivity.
  - rewrite IH. apply sumq_ext. intros x Hx.
    replace (Z.to_nat (x + 1)) with (S (Z.to_nat x)) by lia.
    replace (j0 + Z.to_N (x + 1))%N with (j0 + 1 + Z.to_N x)%N by lia.
    reflexivity.
Qed.

Lemma sol_ext_d : forall A n m (d d' : Z -> Q),
  (forall x, 0 <= x < m -> (d x == d' x)%Q) -> sol A n m d -> sol A n m d'.
Proof.
  intros A n m d d' H Hs i Hi. rewrite <- (Hs i Hi). unfold rowsum. apply sumq_ext.
  intros x Hx. rewrite H by lia. reflexivity.
Qed.

Lemma satisfies_iff : forall (e : list (list Z)) (d : assignment) (m : N),
  Forall (fun row => len row = m) e ->
  (satisfies e d <-> sol (Ae e) (Z.of_nat (List.length e)) (Z.of_N m) (fun x => d (Z.to_N x))).
Proof.
  intros e d m HF. unfold satisfies, sol. rewrite Forall_forall in *.
  assert (Hrow : forall i, 0 <= i < Z.of_nat (List.length e) ->
     (row_value (nth (Z.to_nat i) e []) d 0 ==
      rowsum (Ae e i) (fun x => d (Z.to_N x)) (Z.to_nat (Z.of_N m)))%Q).
  { intros i Hi. rewrite row_value_sumq.
    assert (Hl : List.length (nth (Z.to_nat i) e []) = Z.to_nat (Z.of_N m)).
    { specialize (HF _ (nth_In e [] (n := Z.to_nat i) ltac:(lia))). unfold len in HF. lia. }
    rewrite Hl. unfold rowsum, Ae. apply sumq_ext. intros x Hx. reflexivity. }
  split.
  - intros H i Hi. rewrite <- Hrow by exact Hi. apply H. apply nth_In. lia.
  - intros H row Hin. destruct (In_nth e row [] Hin) as (k & Hk & Ek).
    subst row. specialize (Hrow (Z.of_nat k) ltac:(lia)). rewrite Nat2Z.id in Hrow.
    rewrite Hrow. apply H. lia.
Qed.

Lemma free_iff : forall (e : list (list Z)) (m j : N),
  Forall (fun row => len row = m) e ->
  (free_quantity e j <->
   exists dz, sol (Ae e) (Z.of_nat (List.length e)) (Z.of_N m) dz /\ ~ (dz (Z.of_N j) == 0)%Q).
Proof.
  intros e m j HF. split.
  - intros (d & Hd & Hj). exists (fun x => d (Z.to_N x)). split.
    + apply (proj1 (satisfies_iff e d m HF)). exact Hd.
    + rewrite N2Z.id. exact Hj.
  - intros (dz & Hd & Hj). exists (fun y => dz (Z.of_N y)). split.
    + apply (proj2 (satisfies_iff e _ m HF)).
      apply (sol_ext_d _ _ _ dz); [|exact Hd].
      intros x Hx. rewrite Z2N.id by lia. reflexivity.
    + exact Hj.
Qed.

(* ------------------------------------------------------------------ *)
(* The contract                                                        *)
(* ------------------------------------------------------------------ *)

Lemma bool_match_of_iff : forall (b : bool) (P : Prop),
  (b = true <-> P) -> match b with true => P | false => ~ P end.
Proof.
  intros [|] P [H1 H2]; [exact (H1 eq_refl)|intros HP; discriminate (H2 HP)].
Qed.

Lemma valid_impl_correct :
  forall (m : N) (e : list (list Z)) (xm : uint) (xe : array (array sint)),
  valid_input m e -> repr xm m -> repr xe e ->
  exists b : bool, repr (valid_impl xm xe) b /\ valid_spec m e b.
Proof.
  intros m e xm xe Hv Hm He.
  exists (valid_impl xm xe). split; [reflexivity|].
  destruct Hv as [Hve Hvq Hvr _]. unfold len in Hve.
  assert (Hxm : (φ xm) = Z.of_N m)
    by (cbv [repr repr_uint] in Hm; pose proof (to_Z_bounded xm); lia).
  assert (Hxn : (φ (PArray.length xe)) = Z.of_nat (List.length e))
    by (destruct He as [Hl _]; symmetry; exact Hl).
  unfold valid_impl. cbv zeta.
  set (n := PArray.length xe) in *.
  assert (Hnm : (φ n) * (φ xm) <= 4194303) by (rewrite Hxn, Hxm; nia).
  set (T0 := ztab n xm xe). set (U0 := PArray.make n false).
  destruct (ztab_spec n xm xe Hnm) as [HL0 HT0]. fold T0 in HL0, HT0.
  assert (HU0 : (φ (PArray.length U0)) = (φ n)).
  { unfold U0. rewrite blength_make.
    replace (n <=? max_length)%uint63 with true; [reflexivity|].
    symmetry. rewrite leb_spec, max_length_val. lia. }
  assert (Hcell : forall i x, 0 <= i < (φ n) -> 0 <= x < (φ xm) -> cell T0 (φ xm) i x = Ae e i x).
  { intros i x Hi Hx. rewrite HT0 by lia.
    exact (repr_cells e xe m He Hvr i x ltac:(lia) ltac:(lia)). }
  assert (HI0 : Inv (Ae e) (cell T0 (φ xm)) (fun i => U0.[of_Z i]) (φ n) (φ xm) 0).
  { split.
    - intros d. unfold sol. split; intros H i Hi; rewrite <- (H i Hi); apply rowsum_ext;
        intros x Hx; rewrite Hcell by lia; reflexivity.
    - exists (fun _ => 0). split.
      + intros i Hi Hu. unfold U0 in Hu. rewrite bget_make in Hu. discriminate.
      + intros i Hi Hu k Hk. lia. }
  destruct (col_loop_spec n xm Hnm (Ae e) T0 U0 HL0 HU0 HI0) as [HL [HU [Hsol [piv HP]]]].
  set (st := for_ 0 xm (T0, U0) (col_step n xm)) in *.
  unfold valid_spec. apply bool_match_of_iff. rewrite (final_loop_spec n xm Hnm (fst st)).
  pose proof (to_Z_bounded n) as Bn. pose proof (to_Z_bounded xm) as Bm.
  rewrite (final_iff (Ae e) (cell (fst st) (φ xm)) (fun i => (snd st).[of_Z i]) piv (φ n) (φ xm)); [ | lia | lia | exact HP | exact Hsol].
  rewrite Hxn, Hxm. split.
  - intros H j Hj. apply (free_iff e m j Hvr). apply H. lia.
  - intros H j Hj.
    destruct (proj1 (free_iff e m (Z.to_N j) Hvr) (H (Z.to_N j) ltac:(lia))) as (d & Hd & Hdj).
    exists d. rewrite Z2N.id in Hdj by lia. split; assumption.
Qed.

(* ------------------------------------------------------------------ *)
(* The spec's items, at top level                                      *)
(* ------------------------------------------------------------------ *)

Definition valid : uint -> array (array sint) -> bool := valid_impl.

Definition valid_correct :
  forall (m : N) (e : list (list Z)) (xm : uint) (xe : array (array sint)),
  valid_input m e -> repr xm m -> repr xe e ->
  exists b : bool, repr (valid xm xe) b /\ valid_spec m e b
  := valid_impl_correct.
