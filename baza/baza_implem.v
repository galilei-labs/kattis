(* Implementation of baza (baza.spec): a trie of the database words with
   a counter per node, built once in database order; every query answered
   offline against it.  See README.md, "Implementation". *)

From Baza.spec Require Import Prelude.
From StdGalilei Require Import repr.
From Stdlib Require Import ZArith NArith List Uint63 PArray ZifyUint63 Lia Zwf.
From Stdlib Require String Ascii PrimString.
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

Definition gap (m j : int) : Z := ((φ m) - (φ j))%Z.

Lemma dec_step : forall m i : int,
  (i <? m) = true -> Zwf 0 (gap m (i + 1)) (gap m i).
Proof.
  intros m i H. rewrite ltb_spec in H.
  assert (H1 : (φ (i + 1)) = ((φ i) + 1)%Z) by sia.
  unfold Zwf, gap. lia.
Qed.

(* ------------------------------------------------------------------ *)
(* The 26 child tables: one flat array per letter, indexed by node     *)
(* ------------------------------------------------------------------ *)

Record tab : Type := mkT {
  tc0 : array int;
  tc1 : array int;
  tc2 : array int;
  tc3 : array int;
  tc4 : array int;
  tc5 : array int;
  tc6 : array int;
  tc7 : array int;
  tc8 : array int;
  tc9 : array int;
  tc10 : array int;
  tc11 : array int;
  tc12 : array int;
  tc13 : array int;
  tc14 : array int;
  tc15 : array int;
  tc16 : array int;
  tc17 : array int;
  tc18 : array int;
  tc19 : array int;
  tc20 : array int;
  tc21 : array int;
  tc22 : array int;
  tc23 : array int;
  tc24 : array int;
  tc25 : array int }.
Elpi complexity tab.
Elpi complexity tc0.
Elpi complexity tc1.
Elpi complexity tc2.
Elpi complexity tc3.
Elpi complexity tc4.
Elpi complexity tc5.
Elpi complexity tc6.
Elpi complexity tc7.
Elpi complexity tc8.
Elpi complexity tc9.
Elpi complexity tc10.
Elpi complexity tc11.
Elpi complexity tc12.
Elpi complexity tc13.
Elpi complexity tc14.
Elpi complexity tc15.
Elpi complexity tc16.
Elpi complexity tc17.
Elpi complexity tc18.
Elpi complexity tc19.
Elpi complexity tc20.
Elpi complexity tc21.
Elpi complexity tc22.
Elpi complexity tc23.
Elpi complexity tc24.
Elpi complexity tc25.

Definition sel (t : tab) (c : int) : array int :=
  if c <? 13 then
    if c <? 6 then
      if c <? 3 then
        if c <? 1 then
          tc0 t
        else
          if c <? 2 then
            tc1 t
          else
            tc2 t
      else
        if c <? 4 then
          tc3 t
        else
          if c <? 5 then
            tc4 t
          else
            tc5 t
    else
      if c <? 9 then
        if c <? 7 then
          tc6 t
        else
          if c <? 8 then
            tc7 t
          else
            tc8 t
      else
        if c <? 11 then
          if c <? 10 then
            tc9 t
          else
            tc10 t
        else
          if c <? 12 then
            tc11 t
          else
            tc12 t
  else
    if c <? 19 then
      if c <? 16 then
        if c <? 14 then
          tc13 t
        else
          if c <? 15 then
            tc14 t
          else
            tc15 t
      else
        if c <? 17 then
          tc16 t
        else
          if c <? 18 then
            tc17 t
          else
            tc18 t
    else
      if c <? 22 then
        if c <? 20 then
          tc19 t
        else
          if c <? 21 then
            tc20 t
          else
            tc21 t
      else
        if c <? 24 then
          if c <? 23 then
            tc22 t
          else
            tc23 t
        else
          if c <? 25 then
            tc24 t
          else
            tc25 t.
Elpi complexity sel.

Definition upd (t : tab) (c : int) (a : array int) : tab :=
  if c <? 13 then
    if c <? 6 then
      if c <? 3 then
        if c <? 1 then
          mkT a (tc1 t) (tc2 t) (tc3 t) (tc4 t) (tc5 t) (tc6 t) (tc7 t) (tc8 t) (tc9 t) (tc10 t) (tc11 t) (tc12 t) (tc13 t) (tc14 t) (tc15 t) (tc16 t) (tc17 t) (tc18 t) (tc19 t) (tc20 t) (tc21 t) (tc22 t) (tc23 t) (tc24 t) (tc25 t)
        else
          if c <? 2 then
            mkT (tc0 t) a (tc2 t) (tc3 t) (tc4 t) (tc5 t) (tc6 t) (tc7 t) (tc8 t) (tc9 t) (tc10 t) (tc11 t) (tc12 t) (tc13 t) (tc14 t) (tc15 t) (tc16 t) (tc17 t) (tc18 t) (tc19 t) (tc20 t) (tc21 t) (tc22 t) (tc23 t) (tc24 t) (tc25 t)
          else
            mkT (tc0 t) (tc1 t) a (tc3 t) (tc4 t) (tc5 t) (tc6 t) (tc7 t) (tc8 t) (tc9 t) (tc10 t) (tc11 t) (tc12 t) (tc13 t) (tc14 t) (tc15 t) (tc16 t) (tc17 t) (tc18 t) (tc19 t) (tc20 t) (tc21 t) (tc22 t) (tc23 t) (tc24 t) (tc25 t)
      else
        if c <? 4 then
          mkT (tc0 t) (tc1 t) (tc2 t) a (tc4 t) (tc5 t) (tc6 t) (tc7 t) (tc8 t) (tc9 t) (tc10 t) (tc11 t) (tc12 t) (tc13 t) (tc14 t) (tc15 t) (tc16 t) (tc17 t) (tc18 t) (tc19 t) (tc20 t) (tc21 t) (tc22 t) (tc23 t) (tc24 t) (tc25 t)
        else
          if c <? 5 then
            mkT (tc0 t) (tc1 t) (tc2 t) (tc3 t) a (tc5 t) (tc6 t) (tc7 t) (tc8 t) (tc9 t) (tc10 t) (tc11 t) (tc12 t) (tc13 t) (tc14 t) (tc15 t) (tc16 t) (tc17 t) (tc18 t) (tc19 t) (tc20 t) (tc21 t) (tc22 t) (tc23 t) (tc24 t) (tc25 t)
          else
            mkT (tc0 t) (tc1 t) (tc2 t) (tc3 t) (tc4 t) a (tc6 t) (tc7 t) (tc8 t) (tc9 t) (tc10 t) (tc11 t) (tc12 t) (tc13 t) (tc14 t) (tc15 t) (tc16 t) (tc17 t) (tc18 t) (tc19 t) (tc20 t) (tc21 t) (tc22 t) (tc23 t) (tc24 t) (tc25 t)
    else
      if c <? 9 then
        if c <? 7 then
          mkT (tc0 t) (tc1 t) (tc2 t) (tc3 t) (tc4 t) (tc5 t) a (tc7 t) (tc8 t) (tc9 t) (tc10 t) (tc11 t) (tc12 t) (tc13 t) (tc14 t) (tc15 t) (tc16 t) (tc17 t) (tc18 t) (tc19 t) (tc20 t) (tc21 t) (tc22 t) (tc23 t) (tc24 t) (tc25 t)
        else
          if c <? 8 then
            mkT (tc0 t) (tc1 t) (tc2 t) (tc3 t) (tc4 t) (tc5 t) (tc6 t) a (tc8 t) (tc9 t) (tc10 t) (tc11 t) (tc12 t) (tc13 t) (tc14 t) (tc15 t) (tc16 t) (tc17 t) (tc18 t) (tc19 t) (tc20 t) (tc21 t) (tc22 t) (tc23 t) (tc24 t) (tc25 t)
          else
            mkT (tc0 t) (tc1 t) (tc2 t) (tc3 t) (tc4 t) (tc5 t) (tc6 t) (tc7 t) a (tc9 t) (tc10 t) (tc11 t) (tc12 t) (tc13 t) (tc14 t) (tc15 t) (tc16 t) (tc17 t) (tc18 t) (tc19 t) (tc20 t) (tc21 t) (tc22 t) (tc23 t) (tc24 t) (tc25 t)
      else
        if c <? 11 then
          if c <? 10 then
            mkT (tc0 t) (tc1 t) (tc2 t) (tc3 t) (tc4 t) (tc5 t) (tc6 t) (tc7 t) (tc8 t) a (tc10 t) (tc11 t) (tc12 t) (tc13 t) (tc14 t) (tc15 t) (tc16 t) (tc17 t) (tc18 t) (tc19 t) (tc20 t) (tc21 t) (tc22 t) (tc23 t) (tc24 t) (tc25 t)
          else
            mkT (tc0 t) (tc1 t) (tc2 t) (tc3 t) (tc4 t) (tc5 t) (tc6 t) (tc7 t) (tc8 t) (tc9 t) a (tc11 t) (tc12 t) (tc13 t) (tc14 t) (tc15 t) (tc16 t) (tc17 t) (tc18 t) (tc19 t) (tc20 t) (tc21 t) (tc22 t) (tc23 t) (tc24 t) (tc25 t)
        else
          if c <? 12 then
            mkT (tc0 t) (tc1 t) (tc2 t) (tc3 t) (tc4 t) (tc5 t) (tc6 t) (tc7 t) (tc8 t) (tc9 t) (tc10 t) a (tc12 t) (tc13 t) (tc14 t) (tc15 t) (tc16 t) (tc17 t) (tc18 t) (tc19 t) (tc20 t) (tc21 t) (tc22 t) (tc23 t) (tc24 t) (tc25 t)
          else
            mkT (tc0 t) (tc1 t) (tc2 t) (tc3 t) (tc4 t) (tc5 t) (tc6 t) (tc7 t) (tc8 t) (tc9 t) (tc10 t) (tc11 t) a (tc13 t) (tc14 t) (tc15 t) (tc16 t) (tc17 t) (tc18 t) (tc19 t) (tc20 t) (tc21 t) (tc22 t) (tc23 t) (tc24 t) (tc25 t)
  else
    if c <? 19 then
      if c <? 16 then
        if c <? 14 then
          mkT (tc0 t) (tc1 t) (tc2 t) (tc3 t) (tc4 t) (tc5 t) (tc6 t) (tc7 t) (tc8 t) (tc9 t) (tc10 t) (tc11 t) (tc12 t) a (tc14 t) (tc15 t) (tc16 t) (tc17 t) (tc18 t) (tc19 t) (tc20 t) (tc21 t) (tc22 t) (tc23 t) (tc24 t) (tc25 t)
        else
          if c <? 15 then
            mkT (tc0 t) (tc1 t) (tc2 t) (tc3 t) (tc4 t) (tc5 t) (tc6 t) (tc7 t) (tc8 t) (tc9 t) (tc10 t) (tc11 t) (tc12 t) (tc13 t) a (tc15 t) (tc16 t) (tc17 t) (tc18 t) (tc19 t) (tc20 t) (tc21 t) (tc22 t) (tc23 t) (tc24 t) (tc25 t)
          else
            mkT (tc0 t) (tc1 t) (tc2 t) (tc3 t) (tc4 t) (tc5 t) (tc6 t) (tc7 t) (tc8 t) (tc9 t) (tc10 t) (tc11 t) (tc12 t) (tc13 t) (tc14 t) a (tc16 t) (tc17 t) (tc18 t) (tc19 t) (tc20 t) (tc21 t) (tc22 t) (tc23 t) (tc24 t) (tc25 t)
      else
        if c <? 17 then
          mkT (tc0 t) (tc1 t) (tc2 t) (tc3 t) (tc4 t) (tc5 t) (tc6 t) (tc7 t) (tc8 t) (tc9 t) (tc10 t) (tc11 t) (tc12 t) (tc13 t) (tc14 t) (tc15 t) a (tc17 t) (tc18 t) (tc19 t) (tc20 t) (tc21 t) (tc22 t) (tc23 t) (tc24 t) (tc25 t)
        else
          if c <? 18 then
            mkT (tc0 t) (tc1 t) (tc2 t) (tc3 t) (tc4 t) (tc5 t) (tc6 t) (tc7 t) (tc8 t) (tc9 t) (tc10 t) (tc11 t) (tc12 t) (tc13 t) (tc14 t) (tc15 t) (tc16 t) a (tc18 t) (tc19 t) (tc20 t) (tc21 t) (tc22 t) (tc23 t) (tc24 t) (tc25 t)
          else
            mkT (tc0 t) (tc1 t) (tc2 t) (tc3 t) (tc4 t) (tc5 t) (tc6 t) (tc7 t) (tc8 t) (tc9 t) (tc10 t) (tc11 t) (tc12 t) (tc13 t) (tc14 t) (tc15 t) (tc16 t) (tc17 t) a (tc19 t) (tc20 t) (tc21 t) (tc22 t) (tc23 t) (tc24 t) (tc25 t)
    else
      if c <? 22 then
        if c <? 20 then
          mkT (tc0 t) (tc1 t) (tc2 t) (tc3 t) (tc4 t) (tc5 t) (tc6 t) (tc7 t) (tc8 t) (tc9 t) (tc10 t) (tc11 t) (tc12 t) (tc13 t) (tc14 t) (tc15 t) (tc16 t) (tc17 t) (tc18 t) a (tc20 t) (tc21 t) (tc22 t) (tc23 t) (tc24 t) (tc25 t)
        else
          if c <? 21 then
            mkT (tc0 t) (tc1 t) (tc2 t) (tc3 t) (tc4 t) (tc5 t) (tc6 t) (tc7 t) (tc8 t) (tc9 t) (tc10 t) (tc11 t) (tc12 t) (tc13 t) (tc14 t) (tc15 t) (tc16 t) (tc17 t) (tc18 t) (tc19 t) a (tc21 t) (tc22 t) (tc23 t) (tc24 t) (tc25 t)
          else
            mkT (tc0 t) (tc1 t) (tc2 t) (tc3 t) (tc4 t) (tc5 t) (tc6 t) (tc7 t) (tc8 t) (tc9 t) (tc10 t) (tc11 t) (tc12 t) (tc13 t) (tc14 t) (tc15 t) (tc16 t) (tc17 t) (tc18 t) (tc19 t) (tc20 t) a (tc22 t) (tc23 t) (tc24 t) (tc25 t)
      else
        if c <? 24 then
          if c <? 23 then
            mkT (tc0 t) (tc1 t) (tc2 t) (tc3 t) (tc4 t) (tc5 t) (tc6 t) (tc7 t) (tc8 t) (tc9 t) (tc10 t) (tc11 t) (tc12 t) (tc13 t) (tc14 t) (tc15 t) (tc16 t) (tc17 t) (tc18 t) (tc19 t) (tc20 t) (tc21 t) a (tc23 t) (tc24 t) (tc25 t)
          else
            mkT (tc0 t) (tc1 t) (tc2 t) (tc3 t) (tc4 t) (tc5 t) (tc6 t) (tc7 t) (tc8 t) (tc9 t) (tc10 t) (tc11 t) (tc12 t) (tc13 t) (tc14 t) (tc15 t) (tc16 t) (tc17 t) (tc18 t) (tc19 t) (tc20 t) (tc21 t) (tc22 t) a (tc24 t) (tc25 t)
        else
          if c <? 25 then
            mkT (tc0 t) (tc1 t) (tc2 t) (tc3 t) (tc4 t) (tc5 t) (tc6 t) (tc7 t) (tc8 t) (tc9 t) (tc10 t) (tc11 t) (tc12 t) (tc13 t) (tc14 t) (tc15 t) (tc16 t) (tc17 t) (tc18 t) (tc19 t) (tc20 t) (tc21 t) (tc22 t) (tc23 t) a (tc25 t)
          else
            mkT (tc0 t) (tc1 t) (tc2 t) (tc3 t) (tc4 t) (tc5 t) (tc6 t) (tc7 t) (tc8 t) (tc9 t) (tc10 t) (tc11 t) (tc12 t) (tc13 t) (tc14 t) (tc15 t) (tc16 t) (tc17 t) (tc18 t) (tc19 t) (tc20 t) (tc21 t) (tc22 t) (tc23 t) (tc24 t) a.
Elpi complexity upd.

Definition mk_tab (cap : int) : tab :=
  mkT (PArray.make cap 0) (PArray.make cap 0) (PArray.make cap 0) (PArray.make cap 0) (PArray.make cap 0) (PArray.make cap 0) (PArray.make cap 0) (PArray.make cap 0) (PArray.make cap 0) (PArray.make cap 0) (PArray.make cap 0) (PArray.make cap 0) (PArray.make cap 0) (PArray.make cap 0) (PArray.make cap 0) (PArray.make cap 0) (PArray.make cap 0) (PArray.make cap 0) (PArray.make cap 0) (PArray.make cap 0) (PArray.make cap 0) (PArray.make cap 0) (PArray.make cap 0) (PArray.make cap 0) (PArray.make cap 0) (PArray.make cap 0).
Elpi complexity mk_tab.

(* child of node n by letter c, and its update *)
Definition tget (t : tab) (c n : int) : int := (sel t c).[n].
Definition tset (t : tab) (c n v : int) : tab := upd t c ((sel t c).[n <- v]).
Elpi complexity tget.
Elpi complexity tset.

(* ------------------------------------------------------------------ *)
(* The program                                                         *)
(* ------------------------------------------------------------------ *)

Record ires : Type := mkI
  { r_T : tab; r_cnt : array int; r_sz : int; r_n : int; r_s : int }.
Elpi complexity ires.
Elpi complexity r_T.
Elpi complexity r_cnt.
Elpi complexity r_sz.
Elpi complexity r_n.
Elpi complexity r_s.

(* Insert letters i .. L-1 of w, from node n; sz is the next free node;
   every node on the path gets its counter incremented and the new value
   added to s. *)
Fixpoint ins_loop (w : PrimString.string) (L : int) (T : tab)
    (cnt : array int) (sz i n s : int)
    (H : Acc (Zwf 0) (gap L i)) {struct H} : ires :=
  match bdec (i <? L) with
  | left Hi =>
      let c := PrimString.get w i - 97 in
      let m := tget T c n in
      if m =? 0 then
        ins_loop w L (tset T c n sz) cnt.[sz <- 1] (sz + 1) (i + 1) sz (s + 1)
          (Acc_inv H (dec_step L i Hi))
      else
        let k := cnt.[m] + 1 in
        ins_loop w L T cnt.[m <- k] sz (i + 1) m (s + k)
          (Acc_inv H (dec_step L i Hi))
  | right _ => mkI T cnt sz n s
  end.
Elpi complexity ins_loop.

Lemma ins_loop_eq : forall w L T cnt sz i n s H,
  ins_loop w L T cnt sz i n s H =
  match bdec (i <? L) with
  | left Hi =>
      let c := PrimString.get w i - 97 in
      let m := tget T c n in
      if m =? 0 then
        ins_loop w L (tset T c n sz) cnt.[sz <- 1] (sz + 1) (i + 1) sz (s + 1)
          (Acc_inv H (dec_step L i Hi))
      else
        let k := cnt.[m] + 1 in
        ins_loop w L T cnt.[m <- k] sz (i + 1) m (s + k)
          (Acc_inv H (dec_step L i Hi))
  | right _ => mkI T cnt sz n s
  end.
Proof. intros. destruct H. reflexivity. Qed.

Record bres : Type := mkB { b_T : tab; b_cnt : array int; b_end : array int }.
Elpi complexity bres.
Elpi complexity b_T.
Elpi complexity b_cnt.
Elpi complexity b_end.

(* Insert database words j .. N-1, in order; endv at the node of word j
   receives its answer (j + 1) + s. *)
Fixpoint build (db : array PrimString.string) (N : int) (T : tab)
    (cnt endv : array int) (sz j : int)
    (H : Acc (Zwf 0) (gap N j)) {struct H} : bres :=
  match bdec (j <? N) with
  | left Hj =>
      let w := db.[j] in
      let r := ins_loop w (PrimString.length w) T cnt sz 0 0 0
                 (Zwf_well_founded 0 (gap (PrimString.length w) 0)) in
      build db N (r_T r) (r_cnt r) endv.[r_n r <- j + 1 + r_s r] (r_sz r) (j + 1)
        (Acc_inv H (dec_step N j Hj))
  | right _ => mkB T cnt endv
  end.
Elpi complexity build.

Lemma build_eq : forall db N T cnt endv sz j H,
  build db N T cnt endv sz j H =
  match bdec (j <? N) with
  | left Hj =>
      let w := db.[j] in
      let r := ins_loop w (PrimString.length w) T cnt sz 0 0 0
                 (Zwf_well_founded 0 (gap (PrimString.length w) 0)) in
      build db N (r_T r) (r_cnt r) endv.[r_n r <- j + 1 + r_s r] (r_sz r) (j + 1)
        (Acc_inv H (dec_step N j Hj))
  | right _ => mkB T cnt endv
  end.
Proof. intros. destruct H. reflexivity. Qed.

(* Walk query q from letter i at node n, s the sum of the counters met. *)
Fixpoint qwalk (q : PrimString.string) (L : int) (T : tab) (cnt endv : array int)
    (N i n s : int) (H : Acc (Zwf 0) (gap L i)) {struct H} : int :=
  match bdec (i <? L) with
  | left Hi =>
      let m := tget T (PrimString.get q i - 97) n in
      if m =? 0 then N + s
      else qwalk q L T cnt endv N (i + 1) m (s + cnt.[m])
             (Acc_inv H (dec_step L i Hi))
  | right _ => let e := endv.[n] in if e =? 0 then N + s else e
  end.
Elpi complexity qwalk.

Lemma qwalk_eq : forall q L T cnt endv N i n s H,
  qwalk q L T cnt endv N i n s H =
  match bdec (i <? L) with
  | left Hi =>
      let m := tget T (PrimString.get q i - 97) n in
      if m =? 0 then N + s
      else qwalk q L T cnt endv N (i + 1) m (s + cnt.[m])
             (Acc_inv H (dec_step L i Hi))
  | right _ => let e := endv.[n] in if e =? 0 then N + s else e
  end.
Proof. intros. destruct H. reflexivity. Qed.

Definition query (q : PrimString.string) (T : tab) (cnt endv : array int) (N : int) : int :=
  qwalk q (PrimString.length q) T cnt endv N 0 0 0
    (Zwf_well_founded 0 (gap (PrimString.length q) 0)).
Elpi complexity query.

(* Answer queries k .. Q-1 into out. *)
Fixpoint answer (qs : array PrimString.string) (Q : int) (T : tab)
    (cnt endv : array int) (N : int) (out : array int) (k : int)
    (H : Acc (Zwf 0) (gap Q k)) {struct H} : array int :=
  match bdec (k <? Q) with
  | left Hk =>
      answer qs Q T cnt endv N out.[k <- query qs.[k] T cnt endv N] (k + 1)
        (Acc_inv H (dec_step Q k Hk))
  | right _ => out
  end.
Elpi complexity answer.

Lemma answer_eq : forall qs Q T cnt endv N out k H,
  answer qs Q T cnt endv N out k H =
  match bdec (k <? Q) with
  | left Hk =>
      answer qs Q T cnt endv N out.[k <- query qs.[k] T cnt endv N] (k + 1)
        (Acc_inv H (dec_step Q k Hk))
  | right _ => out
  end.
Proof. intros. destruct H. reflexivity. Qed.

(* acc + the total length of the words j .. N-1 *)
Fixpoint total (db : array PrimString.string) (N j acc : int)
    (H : Acc (Zwf 0) (gap N j)) {struct H} : int :=
  match bdec (j <? N) with
  | left Hj => total db N (j + 1) (acc + PrimString.length db.[j])
                 (Acc_inv H (dec_step N j Hj))
  | right _ => acc
  end.
Elpi complexity total.

Lemma total_eq : forall db N j acc H,
  total db N j acc H =
  match bdec (j <? N) with
  | left Hj => total db N (j + 1) (acc + PrimString.length db.[j])
                 (Acc_inv H (dec_step N j Hj))
  | right _ => acc
  end.
Proof. intros. destruct H. reflexivity. Qed.

Definition baza_impl (db qs : array PrimString.string) : array uint :=
  let N := PArray.length db in
  let cap := 1 + total db N 0 0 (Zwf_well_founded 0 (gap N 0)) in
  let b := build db N (mk_tab cap) (PArray.make cap 0) (PArray.make cap 0) 1 0
             (Zwf_well_founded 0 (gap N 0)) in
  let Q := PArray.length qs in
  answer qs Q (b_T b) (b_cnt b) (b_end b) N (PArray.make Q 0) 0
    (Zwf_well_founded 0 (gap Q 0)).
Elpi complexity baza_impl.


(* ------------------------------------------------------------------ *)
(* Uint63 / PArray plumbing                                            *)
(* ------------------------------------------------------------------ *)

Lemma ltb_reflect : forall x y : int, Bool.reflect ((φ x) < (φ y))%Z (x <? y).
Proof. intros. apply Bool.iff_reflect. symmetry. apply ltb_spec. Qed.

Ltac split_c c :=
  repeat match goal with |- context [c <? ?k] => destruct (ltb_reflect c k) end.

Lemma sel_upd_same : forall t c a, ((φ c) < 26)%Z -> sel (upd t c a) c = a.
Proof. intros t c a Hc. destruct t. unfold sel, upd. split_c c; reflexivity. Qed.

Lemma sel_upd_other : forall t c c' a, ((φ c) < 26)%Z -> ((φ c') < 26)%Z -> c <> c' ->
  sel (upd t c a) c' = sel t c'.
Proof.
  intros t c c' a Hc Hc' Hne. pose proof (to_Z_bounded c). pose proof (to_Z_bounded c').
  destruct t. unfold upd. split_c c; unfold sel; split_c c';
    first [reflexivity | exfalso; apply Hne; apply to_Z_inj; lia].
Qed.

Lemma sel_mk_tab : forall cap c, sel (mk_tab cap) c = PArray.make cap 0.
Proof. intros cap c. unfold sel, mk_tab. split_c c; reflexivity. Qed.

Lemma tget_tset_same : forall t c n v, ((φ c) < 26)%Z ->
  ((φ n) < (φ (PArray.length (sel t c))))%Z -> tget (tset t c n v) c n = v.
Proof.
  intros t c n v Hc Hn. unfold tget, tset. rewrite sel_upd_same by exact Hc.
  exact (get_set_same int (sel t c) n v ltac:(rewrite ltb_spec; exact Hn)).
Qed.

Lemma tget_tset_other : forall t c c' n n' v, ((φ c) < 26)%Z -> ((φ c') < 26)%Z ->
  (c <> c' \/ n <> n') -> tget (tset t c n v) c' n' = tget t c' n'.
Proof.
  intros t c c' n n' v Hc Hc' Hne. unfold tget, tset.
  destruct (c =? c') eqn:E.
  - apply eqb_spec in E. subst c'. rewrite sel_upd_same by exact Hc.
    exact (get_set_other int (sel t c) n n' v
             ltac:(destruct Hne as [Hne | Hne]; [congruence | exact Hne])).
  - apply eqb_false_spec in E. rewrite sel_upd_other by assumption. reflexivity.
Qed.

Lemma len_tset : forall t c c' n v, ((φ c) < 26)%Z -> ((φ c') < 26)%Z ->
  PArray.length (sel (tset t c n v) c') = PArray.length (sel t c').
Proof.
  intros t c c' n v Hc Hc'. unfold tset.
  destruct (c =? c') eqn:E.
  - apply eqb_spec in E. subst c'. rewrite sel_upd_same by exact Hc.
    exact (length_set int (sel t c) n v).
  - apply eqb_false_spec in E. rewrite sel_upd_other by assumption. reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* Math side: a word is the list of its letter indices (code - 97)     *)
(* ------------------------------------------------------------------ *)

Open Scope list_scope.

(* p is a prefix of u *)
Fixpoint preb (p u : list Z) : bool :=
  match p, u with
  | [], _ => true
  | x :: p', y :: u' => Z.eqb x y && preb p' u'
  | _ :: _, [] => false
  end.

(* how many words of W start with p *)
Definition cntW (W : list (list Z)) (p : list Z) : nat :=
  list_sum (map (fun v => if preb p v then 1%nat else 0%nat) W).

(* p is the root or the prefix of a word of W: the strings with a node *)
Definition SW (W : list (list Z)) (p : list Z) : Prop :=
  p = [] \/ exists v, In v W /\ preb p v = true.

Definition sumlen (W : list (list Z)) : nat := list_sum (map (@List.length Z) W).

Fixpoint sumn (f : nat -> nat) (n : nat) : nat :=
  match n with O => O | S n' => (sumn f n' + f n')%nat end.

(* the sum of the counters met on the path of q *)
Definition pathsum (W : list (list Z)) (q : list Z) : nat :=
  sumn (fun l => cntW W (firstn (S l) q)) (List.length q).

Fixpoint index_of (p : list Z) (W : list (list Z)) : option nat :=
  match W with
  | [] => None
  | v :: W' => if list_eq_dec Z.eq_dec p v then Some O
               else option_map S (index_of p W')
  end.

(* the value stored at the end node of p *)
Definition EW (W : list (list Z)) (p : list Z) : Z :=
  match index_of p W with
  | Some k => Z.of_nat (S k + pathsum (firstn (S k) W) p)
  | None => 0%Z
  end.

(* the answer to query q *)
Definition ansm (W : list (list Z)) (q : list Z) : nat :=
  match index_of q W with
  | Some k => (S k + pathsum (firstn (S k) W) q)%nat
  | None => (List.length W + pathsum W q)%nat
  end.

Lemma preb_spec : forall p u, preb p u = true <-> exists r, u = p ++ r.
Proof.
  induction p as [|x p IH]; intros [|y u]; simpl.
  - split; [intros _; exists []; reflexivity | reflexivity].
  - split; [intros _; exists (y :: u); reflexivity | reflexivity].
  - split; [discriminate | intros [r Hr]; discriminate].
  - split.
    + intros H. apply andb_prop in H as [H1 H2]. apply Z.eqb_eq in H1. subst y.
      apply IH in H2 as [r ->]. exists r. reflexivity.
    + intros [r Hr]. injection Hr as -> ->. rewrite Z.eqb_refl. simpl.
      apply IH. exists r. reflexivity.
Qed.

Lemma preb_app : forall p r, preb p (p ++ r) = true.
Proof. intros p r. apply preb_spec. exists r. reflexivity. Qed.

Lemma preb_refl : forall p, preb p p = true.
Proof. intros p. rewrite <- (app_nil_r p) at 2. apply preb_app. Qed.

Lemma preb_trans : forall p q u, preb p q = true -> preb q u = true -> preb p u = true.
Proof.
  intros p q u H1 H2. apply preb_spec in H1 as [r1 ->]. apply preb_spec in H2 as [r2 ->].
  rewrite <- app_assoc. apply preb_app.
Qed.

Lemma preb_len : forall p u, preb p u = true -> (List.length p <= List.length u)%nat.
Proof. intros p u H. apply preb_spec in H as [r ->]. rewrite length_app. lia. Qed.

Lemma preb_nil_r : forall p, preb p [] = true -> p = [].
Proof. intros [|x p] H; [reflexivity | discriminate]. Qed.

Lemma preb_snoc : forall p q x,
  preb p (q ++ [x]) = true <-> p = q ++ [x] \/ preb p q = true.
Proof.
  intros p q x. split.
  - intros H. apply preb_spec in H as [r Hr].
    destruct r as [|a l' _] using rev_ind.
    + left. rewrite app_nil_r in Hr. symmetry. exact Hr.
    + rewrite app_assoc in Hr.
      apply app_inj_tail in Hr as [Hq _]. right. apply preb_spec. exists l'. exact Hq.
  - intros [-> | H]; [apply preb_refl | eapply preb_trans; [exact H | apply preb_app]].
Qed.

Lemma preb_firstn : forall l u, preb (firstn l u) u = true.
Proof. intros l u. rewrite <- (firstn_skipn l u) at 2. apply preb_app. Qed.

Lemma SW_closed : forall W p q, preb p q = true -> SW W q -> SW W p.
Proof.
  intros W p q H [-> | [v [Hv Hq]]].
  - left. apply preb_nil_r. exact H.
  - right. exists v. split; [exact Hv | eapply preb_trans; eassumption].
Qed.

Lemma SW_snoc_iff : forall W v p, SW (W ++ [v]) p <-> SW W p \/ preb p v = true.
Proof.
  intros W v p. unfold SW. split.
  - intros [-> | [v' [Hv Hp]]]; [left; left; reflexivity|].
    apply in_app_iff in Hv as [Hv | [<- | []]].
    + left. right. exists v'. auto.
    + right. exact Hp.
  - intros [[-> | [v' [Hv Hp]]] | Hp].
    + left. reflexivity.
    + right. exists v'. split; [apply in_app_iff; left; exact Hv | exact Hp].
    + right. exists v. split; [apply in_app_iff; right; left; reflexivity | exact Hp].
Qed.

Lemma cntW_cons : forall v W p,
  cntW (v :: W) p = ((if preb p v then 1 else 0) + cntW W p)%nat.
Proof. reflexivity. Qed.

Lemma cntW_app : forall W v p,
  cntW (W ++ [v]) p = (cntW W p + (if preb p v then 1 else 0))%nat.
Proof.
  intros W v p. unfold cntW. rewrite map_app, list_sum_app. simpl. lia.
Qed.

Lemma cntW_le : forall W p, (cntW W p <= List.length W)%nat.
Proof.
  induction W as [|v W IH]; intros p; [reflexivity|].
  rewrite cntW_cons. simpl. specialize (IH p). destruct (preb p v); lia.
Qed.

Lemma cntW_notS : forall W p, ~ SW W p -> cntW W p = 0%nat.
Proof.
  induction W as [|v W IH]; intros p H; [reflexivity|].
  rewrite cntW_cons. destruct (preb p v) eqn:E.
  - exfalso. apply H. right. exists v. split; [left; reflexivity | exact E].
  - simpl. apply IH. intros [Hp | [v' [Hv Hp]]]; apply H; [left; exact Hp|].
    right. exists v'. split; [right; exact Hv | exact Hp].
Qed.

Lemma sumlen_app : forall W v, sumlen (W ++ [v]) = (sumlen W + List.length v)%nat.
Proof. intros W v. unfold sumlen. rewrite map_app, list_sum_app. simpl. lia. Qed.

Lemma sumn_ext : forall f g n, (forall l, (l < n)%nat -> f l = g l) -> sumn f n = sumn g n.
Proof.
  intros f g n. induction n as [|n IH]; intros H; [reflexivity|].
  simpl. rewrite IH by (intros; apply H; lia). rewrite H by lia. reflexivity.
Qed.

Lemma sumn_le : forall f n b, (forall l, (l < n)%nat -> (f l <= b)%nat) ->
  (sumn f n <= n * b)%nat.
Proof.
  intros f n b. induction n as [|n IH]; intros H; [simpl; lia|].
  simpl. specialize (IH ltac:(intros; apply H; lia)). specialize (H n ltac:(lia)). lia.
Qed.

Lemma index_of_some : forall p W k, index_of p W = Some k -> nth_error W k = Some p.
Proof.
  intros p W. induction W as [|v W IH]; intros k H; simpl in H; [discriminate|].
  destruct (list_eq_dec Z.eq_dec p v) as [-> | Hne].
  - injection H as <-. reflexivity.
  - destruct (index_of p W) as [k'|] eqn:E; simpl in H; [|discriminate].
    injection H as <-. simpl. apply IH. reflexivity.
Qed.

Lemma index_of_none : forall p W, index_of p W = None <-> ~ In p W.
Proof.
  intros p W. induction W as [|v W IH]; simpl.
  - split; [intros _ [] | reflexivity].
  - destruct (list_eq_dec Z.eq_dec p v) as [-> | Hne].
    + split; [discriminate | intros H; exfalso; apply H; left; reflexivity].
    + destruct (index_of p W) as [k'|] eqn:E; simpl.
      * split; [discriminate|]. intros H. exfalso. apply H. right.
        apply nth_error_In with k'. apply index_of_some. exact E.
      * split; [|reflexivity]. intros _ [H | H]; [congruence|].
        apply IH in H; [exact H | reflexivity].
Qed.

Lemma index_of_lt : forall p W k, index_of p W = Some k -> (k < List.length W)%nat.
Proof.
  intros p W k H. apply index_of_some in H. apply nth_error_Some. congruence.
Qed.

Lemma index_of_app_ne : forall p W v, p <> v -> index_of p (W ++ [v]) = index_of p W.
Proof.
  intros p W v Hne. induction W as [|v' W IH]; simpl.
  - destruct (list_eq_dec Z.eq_dec p v); [contradiction | reflexivity].
  - rewrite IH. reflexivity.
Qed.

Lemma index_of_app_last : forall W v, ~ In v W -> index_of v (W ++ [v]) = Some (List.length W).
Proof.
  induction W as [|v' W IH]; intros v H; simpl.
  - destruct (list_eq_dec Z.eq_dec v v); [reflexivity | contradiction].
  - destruct (list_eq_dec Z.eq_dec v v') as [-> | Hne].
    + exfalso. apply H. left. reflexivity.
    + rewrite IH by (intros H'; apply H; right; exact H'). reflexivity.
Qed.

Lemma EW_app_ne : forall W v p, p <> v -> EW (W ++ [v]) p = EW W p.
Proof.
  intros W v p Hne. unfold EW. rewrite index_of_app_ne by exact Hne.
  destruct (index_of p W) as [k|] eqn:E; [|reflexivity].
  apply index_of_lt in E. rewrite firstn_app.
  replace (S k - List.length W)%nat with O by lia. rewrite app_nil_r. reflexivity.
Qed.

Lemma EW_app_last : forall W v, ~ In v W ->
  EW (W ++ [v]) v = Z.of_nat (S (List.length W) + pathsum (W ++ [v]) v).
Proof.
  intros W v H. unfold EW. rewrite index_of_app_last by exact H.
  rewrite firstn_all2; [reflexivity|]. rewrite length_app. simpl. lia.
Qed.

Lemma preb_snoc_ne : forall p pre x, p <> pre ++ [x] -> preb p (pre ++ [x]) = preb p pre.
Proof.
  intros p pre x Hp. destruct (preb p pre) eqn:E1.
  - apply preb_snoc. right. exact E1.
  - destruct (preb p (pre ++ [x])) eqn:E2; [|reflexivity].
    apply preb_snoc in E2 as [E2|E2]; congruence.
Qed.

Lemma preb_snoc_short : forall pre x, preb (pre ++ [x]) pre = false.
Proof.
  intros pre x. destruct (preb (pre ++ [x]) pre) eqn:E; [|reflexivity].
  apply preb_len in E. rewrite length_app in E. simpl in E. lia.
Qed.

(* ------------------------------------------------------------------ *)
(* Array plumbing at a fixed universe                                  *)
(* ------------------------------------------------------------------ *)

Lemma wB_val : wB = 9223372036854775808%Z.
Proof. reflexivity. Qed.

Lemma max_length_val : (φ PArray.max_length) = 4194303%Z.
Proof. reflexivity. Qed.

Lemma alength_set : forall (t : array int) (i : int) (b : int),
  PArray.length t.[i <- b] = PArray.length t.
Proof. intros t i b. exact (length_set int t i b). Qed.

Lemma aget_set_same : forall (t : array int) (i : int) (b : int),
  ((φ i) < (φ (PArray.length t)))%Z -> t.[i <- b].[i] = b.
Proof. intros t i b H. exact (get_set_same int t i b ltac:(rewrite ltb_spec; exact H)). Qed.

Lemma aget_set_other : forall (t : array int) (i j : int) (b : int),
  i <> j -> t.[i <- b].[j] = t.[j].
Proof. intros t i j b H. exact (get_set_other int t i j b H). Qed.

Lemma alength_make : forall (n : int) (b : int),
  ((φ n) <= 4194303)%Z -> PArray.length (PArray.make n b) = n.
Proof.
  intros n b H.
  transitivity (if n <=? PArray.max_length then n else PArray.max_length);
    [exact (length_make int n b)|].
  replace (n <=? PArray.max_length) with true; [reflexivity|].
  symmetry. rewrite leb_spec, max_length_val. exact H.
Qed.

Lemma aget_make : forall (n i : int) (b : int), (PArray.make n b).[i] = b.
Proof. intros n i b. exact (get_make int b n i). Qed.

Lemma alength_bound : forall (t : array int), ((φ (PArray.length t)) <= 4194303)%Z.
Proof.
  intros t. pose proof (leb_length int t) as H.
  rewrite leb_spec, max_length_val in H. exact H.
Qed.

(* ------------------------------------------------------------------ *)
(* The trie invariant                                                  *)
(* ------------------------------------------------------------------ *)

(* lbl n is the string of node n.  Wc: the words whose prefixes have
   nodes and are counted; We: the words whose end node holds its value. *)
Record Inv (T : tab) (cnt endv : array int) (sz : int) (lbl : int -> list Z)
    (Wc We : list (list Z)) : Prop := {
  iv_len_c : forall c, ((φ c) < 26)%Z -> PArray.length (sel T c) = PArray.length cnt;
  iv_len_e : PArray.length endv = PArray.length cnt;
  iv_sz : (1 <= (φ sz) <= (φ (PArray.length cnt)))%Z;
  iv_cap : ((φ sz) <= 1 + Z.of_nat (sumlen Wc))%Z;
  iv_root : lbl 0 = [];
  iv_inj : forall n m, ((φ n) < (φ sz))%Z -> ((φ m) < (φ sz))%Z -> lbl n = lbl m -> n = m;
  iv_S : forall n, ((φ n) < (φ sz))%Z -> SW Wc (lbl n);
  iv_child : forall n c, ((φ n) < (φ sz))%Z -> ((φ c) < 26)%Z ->
      (tget T c n <> 0 ->
         ((φ (tget T c n)) < (φ sz))%Z /\ lbl (tget T c n) = lbl n ++ [(φ c)]) /\
      (tget T c n = 0 -> ~ SW Wc (lbl n ++ [(φ c)]));
  iv_fresh : forall n c, ((φ sz) <= (φ n) < (φ (PArray.length cnt)))%Z -> ((φ c) < 26)%Z ->
      tget T c n = 0 /\ endv.[n] = 0;
  iv_cnt : forall n, (0 < (φ n) < (φ sz))%Z -> (φ (cnt.[n])) = Z.of_nat (cntW Wc (lbl n));
  iv_end : forall n, ((φ n) < (φ sz))%Z -> (φ (endv.[n])) = EW We (lbl n);
}.

Lemma lt_succ_cases : forall k sz : int, (φ (sz + 1)) = ((φ sz) + 1)%Z ->
  ((φ k) < (φ (sz + 1)))%Z -> k = sz \/ ((φ k) < (φ sz))%Z.
Proof.
  intros k sz H1 H2. destruct (Z.eq_dec (φ k) (φ sz)) as [E | E].
  - left. apply to_Z_inj. exact E.
  - right. lia.
Qed.

Lemma ins_step_new : forall T cnt endv sz lbl W0 pre x n c,
  Inv T cnt endv sz lbl (W0 ++ [pre]) W0 ->
  ((φ n) < (φ sz))%Z -> lbl n = pre -> (φ c) = x -> ((φ c) < 26)%Z -> tget T c n = 0 ->
  ((φ sz) < (φ (PArray.length cnt)))%Z ->
  Inv (tset T c n sz) cnt.[sz <- 1] endv (sz + 1)
      (fun k => if k =? sz then pre ++ [x] else lbl k) (W0 ++ [pre ++ [x]]) W0.
Proof.
  intros T cnt endv sz lbl W0 pre x n c HI Hn Hln Hcx Hc Ht0 Hcap.
  destruct HI as [Hlc Hle Hsz Hcp Hroot Hinj HS Hch Hfr Hcnt Hend].
  pose proof (alength_bound cnt) as Bc.
  assert (Hsz1 : (φ (sz + 1)) = ((φ sz) + 1)%Z) by sia.
  assert (HnS : ~ SW (W0 ++ [pre]) (pre ++ [x])).
  { destruct (Hch n c Hn Hc) as [_ H]. rewrite Hln, Hcx in H. exact (H Ht0). }
  assert (HnS0 : ~ SW W0 (pre ++ [x])).
  { intros H. apply HnS. apply SW_snoc_iff. left. exact H. }
  assert (Hne : forall k, ((φ k) < (φ sz))%Z -> lbl k <> pre ++ [x]).
  { intros k Hk E. apply HnS. rewrite <- E. apply HS. exact Hk. }
  assert (Lsz : forall k, (k =? sz) = false -> True) by auto.
  set (lbl' := fun k => if k =? sz then pre ++ [x] else lbl k).
  assert (Lold : forall k, ((φ k) < (φ sz))%Z -> lbl' k = lbl k).
  { intros k Hk. unfold lbl'. replace (k =? sz) with false; [reflexivity|].
    symmetry. apply eqb_false_spec. intros ->. lia. }
  assert (Lnew : lbl' sz = pre ++ [x]).
  { unfold lbl'. rewrite eqb_refl. reflexivity. }
  assert (Hnsz : n <> sz) by (intros ->; lia).
  assert (Hold_new : forall p, SW (W0 ++ [pre]) p -> SW (W0 ++ [pre ++ [x]]) p).
  { intros p H. apply SW_snoc_iff in H as [H | H]; apply SW_snoc_iff; [left; exact H|].
    right. eapply preb_trans; [exact H | apply preb_app]. }
  constructor.
  - intros c' Hc'. rewrite len_tset by assumption. rewrite alength_set. apply Hlc. exact Hc'.
  - rewrite alength_set. exact Hle.
  - rewrite alength_set. lia.
  - rewrite sumlen_app, length_app. rewrite sumlen_app in Hcp.
    change (List.length [x]) with 1%nat. lia.
  - rewrite Lold by lia. exact Hroot.
  - intros k1 k2 Hk1 Hk2 E.
    destruct (lt_succ_cases k1 sz Hsz1 Hk1) as [-> | H1];
      destruct (lt_succ_cases k2 sz Hsz1 Hk2) as [-> | H2]; [reflexivity | | |].
    + rewrite Lnew, Lold in E by exact H2. exfalso. exact (Hne k2 H2 (eq_sym E)).
    + rewrite Lnew, Lold in E by exact H1. exfalso. exact (Hne k1 H1 E).
    + rewrite !Lold in E by assumption. apply Hinj; assumption.
  - intros k Hk. destruct (lt_succ_cases k sz Hsz1 Hk) as [-> | H1].
    + rewrite Lnew. right. exists (pre ++ [x]). split; [|apply preb_refl].
      apply in_app_iff. right. left. reflexivity.
    + rewrite Lold by exact H1. apply Hold_new. apply HS. exact H1.
  - intros k c' Hk Hc'.
    destruct (lt_succ_cases k sz Hsz1 Hk) as [-> | H1].
    + rewrite tget_tset_other by (try assumption; right; exact Hnsz).
      destruct (Hfr sz c' ltac:(lia) Hc') as [Hz _]. rewrite Hz.
      split; [intros F; contradiction F; reflexivity|]. intros _.
      rewrite Lnew. intros H. apply SW_snoc_iff in H as [H | H].
      * apply HnS0. eapply SW_closed; [|exact H]. apply preb_app.
      * apply preb_len in H. rewrite !length_app in H. simpl in H. lia.
    + rewrite (Lold k H1).
      destruct (Uint63.eqb c c' && Uint63.eqb k n)%bool eqn:Ecn.
      * apply andb_prop in Ecn as [E1 E2]. apply eqb_spec in E1, E2. subst c' k.
        rewrite tget_tset_same by (try assumption; rewrite Hlc by exact Hc; lia).
        split; [|intros F; exfalso; rewrite F in Hsz; change (φ 0) with 0%Z in Hsz; lia].
        intros _. split; [lia|]. rewrite Lnew, Hln, Hcx. reflexivity.
      * rewrite tget_tset_other; [| assumption | assumption |].
        2:{ apply Bool.andb_false_iff in Ecn as [E | E]; apply eqb_false_spec in E;
            [left | right; intros F; apply E; symmetry]; congruence. }
        destruct (Hch k c' H1 Hc') as [Hy Hz]. split.
        -- intros Hm. destruct (Hy Hm) as [Hm1 Hm2]. split; [lia|].
           rewrite Lold by exact Hm1. exact Hm2.
        -- intros Hm H. apply SW_snoc_iff in H as [H | H].
           ++ apply (Hz Hm). apply SW_snoc_iff. left. exact H.
           ++ apply preb_snoc in H as [H | H].
              ** apply app_inj_tail in H as [H2 H3].
                 assert (k = n) by (apply Hinj; [exact H1 | exact Hn | congruence]).
                 assert (c' = c) by (apply to_Z_inj; lia).
                 subst. rewrite !eqb_refl in Ecn. discriminate.
              ** apply (Hz Hm). apply SW_snoc_iff. right. exact H.
  - intros k c' Hk Hc'. rewrite alength_set in Hk.
    rewrite tget_tset_other by (try assumption; right; intros ->; lia).
    apply Hfr; [lia | exact Hc'].
  - intros k Hk. destruct (lt_succ_cases k sz Hsz1 ltac:(lia)) as [-> | H1].
    + rewrite aget_set_same by lia. rewrite Lnew, cntW_app, preb_refl.
      rewrite (cntW_notS W0 _ HnS0). reflexivity.
    + rewrite aget_set_other by (intros ->; lia). rewrite (Lold k H1), Hcnt by lia.
      rewrite !cntW_app. rewrite preb_snoc_ne by (apply Hne; exact H1). reflexivity.
  - intros k Hk. destruct (lt_succ_cases k sz Hsz1 Hk) as [-> | H1].
    + destruct (Hfr sz c ltac:(lia) Hc) as [_ Hz]. rewrite Hz, Lnew.
      unfold EW. replace (index_of (pre ++ [x]) W0) with (@None nat); [reflexivity|].
      symmetry. apply index_of_none. intros H. apply HnS0. right.
      exists (pre ++ [x]). split; [exact H | apply preb_refl].
    + rewrite (Lold k H1). apply Hend. exact H1.
Qed.

Lemma ins_step_old : forall T cnt endv sz lbl W0 pre x n c,
  Inv T cnt endv sz lbl (W0 ++ [pre]) W0 ->
  (Z.of_nat (List.length W0) <= 30000)%Z ->
  ((φ n) < (φ sz))%Z -> lbl n = pre -> (φ c) = x -> ((φ c) < 26)%Z -> tget T c n <> 0 ->
  Inv T cnt.[tget T c n <- cnt.[tget T c n] + 1] endv sz lbl (W0 ++ [pre ++ [x]]) W0 /\
  (φ (cnt.[tget T c n] + 1)) = Z.of_nat (S (cntW W0 (pre ++ [x]))) /\
  ((φ (tget T c n)) < (φ sz))%Z /\ lbl (tget T c n) = pre ++ [x].
Proof.
  intros T cnt endv sz lbl W0 pre x n c HI HW Hn Hln Hcx Hc Hm0.
  destruct HI as [Hlc Hle Hsz Hcp Hroot Hinj HS Hch Hfr Hcnt Hend].
  destruct (proj1 (Hch n c Hn Hc) Hm0) as [Hmsz Hlm].
  rewrite Hln, Hcx in Hlm.
  set (m := tget T c n) in *.
  assert (Hmpos : (0 < (φ m))%Z).
  { pose proof (to_Z_bounded m). destruct (Z.eq_dec (φ m) 0) as [E|E]; [|lia].
    exfalso. apply Hm0. apply to_Z_inj. exact E. }
  assert (HSm : SW (W0 ++ [pre]) (pre ++ [x])) by (rewrite <- Hlm; apply HS; exact Hmsz).
  assert (Hiff : forall p, SW (W0 ++ [pre ++ [x]]) p <-> SW (W0 ++ [pre]) p).
  { intros p. split.
    - intros H. apply SW_snoc_iff in H as [H | H].
      + apply SW_snoc_iff. left. exact H.
      + eapply SW_closed; [exact H | exact HSm].
    - intros H. apply SW_snoc_iff in H as [H | H]; apply SW_snoc_iff; [left; exact H|].
      right. eapply preb_trans; [exact H | apply preb_app]. }
  assert (Hcm : (φ (cnt.[m] + 1)) = Z.of_nat (S (cntW W0 (pre ++ [x])))).
  { assert (Hc0 : (φ (cnt.[m])) = Z.of_nat (cntW W0 (pre ++ [x]))).
    { rewrite Hcnt by lia. rewrite Hlm, cntW_app, preb_snoc_short. lia. }
    pose proof (cntW_le W0 (pre ++ [x])).
    rewrite add_spec, Hc0. change (φ 1) with 1%Z. rewrite wB_val.
    rewrite Z.mod_small; lia. }
  split; [|split; [exact Hcm | split; [exact Hmsz | exact Hlm]]].
  constructor.
  - intros c' Hc'. rewrite alength_set. apply Hlc. exact Hc'.
  - rewrite alength_set. exact Hle.
  - rewrite alength_set. exact Hsz.
  - rewrite sumlen_app, length_app. rewrite sumlen_app in Hcp.
    change (List.length [x]) with 1%nat. lia.
  - exact Hroot.
  - exact Hinj.
  - intros k Hk. apply Hiff. apply HS. exact Hk.
  - intros k c' Hk Hc'. destruct (Hch k c' Hk Hc') as [Hy Hz]. split; [exact Hy|].
    intros H0 H. apply (Hz H0). apply Hiff. exact H.
  - intros k c' Hk Hc'. rewrite alength_set in Hk. apply Hfr; assumption.
  - intros k Hk. destruct (k =? m) eqn:E.
    + apply eqb_spec in E. subst k.
      rewrite aget_set_same by lia.
      rewrite Hcm, Hlm, cntW_app, preb_refl. lia.
    + apply eqb_false_spec in E. rewrite aget_set_other by (intros F; apply E; symmetry; exact F).
      rewrite Hcnt by exact Hk. rewrite !cntW_app. rewrite preb_snoc_ne; [reflexivity|].
      intros F. apply E. apply Hinj; [lia | exact Hmsz | congruence].
  - exact Hend.
Qed.

Lemma Inv_nil : forall T cnt endv sz lbl W0 We,
  Inv T cnt endv sz lbl W0 We -> Inv T cnt endv sz lbl (W0 ++ [[]]) We.
Proof.
  intros T cnt endv sz lbl W0 We HI.
  destruct HI as [Hlc Hle Hsz Hcp Hroot Hinj HS Hch Hfr Hcnt Hend].
  assert (Hiff : forall p, SW (W0 ++ [[]]) p <-> SW W0 p).
  { intros p. rewrite SW_snoc_iff. split; [|left; assumption].
    intros [H | H]; [exact H | left; apply preb_nil_r; exact H]. }
  constructor; try assumption.
  - rewrite sumlen_app. change (List.length (@nil Z)) with 0%nat. lia.
  - intros k Hk. apply Hiff. apply HS. exact Hk.
  - intros k c Hk Hc. destruct (Hch k c Hk Hc) as [Hy Hz]. split; [exact Hy|].
    intros H0 H. apply (Hz H0). apply Hiff. exact H.
  - intros k Hk. rewrite Hcnt by exact Hk. rewrite cntW_app.
    destruct (preb (lbl k) []) eqn:E; [|lia].
    apply preb_nil_r in E. rewrite <- Hroot in E.
    apply Hinj in E; [| lia | lia]. subst k. change (φ 0) with 0%Z in Hk. lia.
Qed.

Lemma Inv_end : forall T cnt endv sz lbl Wc W0 n u v,
  Inv T cnt endv sz lbl Wc W0 -> ((φ n) < (φ sz))%Z -> lbl n = u -> ~ In u W0 ->
  (φ v) = EW (W0 ++ [u]) u ->
  Inv T cnt endv.[n <- v] sz lbl Wc (W0 ++ [u]).
Proof.
  intros T cnt endv sz lbl Wc W0 n u v HI Hn Hln Hu Hv.
  destruct HI as [Hlc Hle Hsz Hcp Hroot Hinj HS Hch Hfr Hcnt Hend].
  constructor; try assumption.
  - rewrite alength_set. exact Hle.
  - intros k c Hk Hc. rewrite aget_set_other by (intros ->; lia). apply Hfr; assumption.
  - intros k Hk. destruct (k =? n) eqn:E.
    + apply eqb_spec in E. subst k. rewrite aget_set_same by (rewrite Hle; lia).
      rewrite Hln. exact Hv.
    + apply eqb_false_spec in E. rewrite aget_set_other by (intros F; apply E; symmetry; exact F).
      rewrite EW_app_ne; [apply Hend; exact Hk|].
      intros F. apply E. apply Hinj; [exact Hk | exact Hn | congruence].
Qed.

(* ------------------------------------------------------------------ *)
(* The insertion loop                                                  *)
(* ------------------------------------------------------------------ *)

(* w is read as the letter indices u *)
Definition wrep (w : PrimString.string) (u : list Z) : Prop :=
  (φ (PrimString.length w)) = Z.of_nat (List.length u) /\
  forall i : int, ((φ i) < (φ (PrimString.length w)))%Z ->
    nth_error u (Z.to_nat (φ i)) = Some (φ (PrimString.get w i - 97)) /\
    ((φ (PrimString.get w i - 97)) < 26)%Z.

Lemma firstn_snoc : forall {A} (u : list A) i x, nth_error u i = Some x ->
  firstn (S i) u = firstn i u ++ [x].
Proof.
  intros A u. induction u as [|y u IH]; intros i x H; [destruct i; discriminate|].
  destruct i as [|i]; simpl in H.
  - injection H as ->. reflexivity.
  - change (firstn (S (S i)) (y :: u)) with (y :: firstn (S i) u).
    rewrite (IH i x H). reflexivity.
Qed.

Definition stepsum (W0 : list (list Z)) (u : list Z) (i : nat) : nat :=
  sumn (fun l => S (cntW W0 (firstn (S l) u))) i.

Lemma stepsum_bound : forall W0 u i,
  (stepsum W0 u i <= i * (List.length W0 + 1))%nat.
Proof.
  intros W0 u i. apply sumn_le. intros l _. pose proof (cntW_le W0 (firstn (S l) u)). lia.
Qed.

Lemma ins_spec : forall w u W0, wrep w u ->
  (Z.of_nat (List.length u) < 30)%Z -> (Z.of_nat (List.length W0) <= 30000)%Z ->
  forall z i T cnt endv sz n s lbl (H : Acc (Zwf 0) (gap (PrimString.length w) i)),
  gap (PrimString.length w) i = z ->
  ((φ i) <= (φ (PrimString.length w)))%Z ->
  Inv T cnt endv sz lbl (W0 ++ [firstn (Z.to_nat (φ i)) u]) W0 ->
  (1 + Z.of_nat (sumlen (W0 ++ [u])) <= (φ (PArray.length cnt)))%Z ->
  ((φ n) < (φ sz))%Z -> lbl n = firstn (Z.to_nat (φ i)) u ->
  (φ s) = Z.of_nat (stepsum W0 u (Z.to_nat (φ i))) ->
  forall r, r = ins_loop w (PrimString.length w) T cnt sz i n s H ->
  PArray.length (r_cnt r) = PArray.length cnt /\
  exists lbl', Inv (r_T r) (r_cnt r) endv (r_sz r) lbl' (W0 ++ [u]) W0 /\
    ((φ (r_n r)) < (φ (r_sz r)))%Z /\ lbl' (r_n r) = u /\
    (φ (r_s r)) = Z.of_nat (stepsum W0 u (List.length u)).
Proof.
  intros w u W0 Hw Hu HW z.
  induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros i T cnt endv sz n s lbl H Hz Hi HI Hcap Hn Hln Hs r Hr.
  rewrite ins_loop_eq in Hr.
  pose proof Hw as [Hwl Hwc].
  pose proof (to_Z_bounded i) as Bi.
  destruct (bdec (i <? PrimString.length w)) as [Hi' | Hi'].
  - pose proof Hi' as Hlt. rewrite ltb_spec in Hlt.
    destruct (Hwc i Hlt) as [Hx Hc26].
    cbv zeta in Hr.
    set (c := PrimString.get w i - 97) in *.
    set (pre := firstn (Z.to_nat (φ i)) u) in *.
    assert (Hfs : firstn (S (Z.to_nat (φ i))) u = pre ++ [(φ c)])
      by (apply firstn_snoc; exact Hx).
    assert (Hi1 : (φ (i + 1)) = ((φ i) + 1)%Z) by sia.
    assert (Hti : Z.to_nat (φ (i + 1)) = S (Z.to_nat (φ i))) by lia.
    assert (Hdec : Zwf 0 (gap (PrimString.length w) (i + 1)) z)
      by (rewrite <- Hz; apply dec_step; exact Hi').
    assert (Bs : (Z.of_nat (stepsum W0 u (S (Z.to_nat (φ i)))) <= 900030)%Z).
    { pose proof (stepsum_bound W0 u (S (Z.to_nat (φ i)))) as Bs.
      apply Nat2Z.inj_le in Bs. rewrite Nat2Z.inj_mul in Bs. nia. }
    assert (Hss : stepsum W0 u (S (Z.to_nat (φ i))) =
                    (stepsum W0 u (Z.to_nat (φ i)) + S (cntW W0 (pre ++ [(φ c)])))%nat)
      by (unfold stepsum; cbn [sumn]; rewrite Hfs; reflexivity).
    destruct (tget T c n =? 0) eqn:Et.
    + apply eqb_spec in Et.
      assert (Hszc : ((φ sz) < (φ (PArray.length cnt)))%Z).
      { pose proof (iv_cap _ _ _ _ _ _ _ HI) as Hc.
        rewrite !sumlen_app in *. unfold pre in Hc. rewrite length_firstn in Hc. lia. }
      pose proof (iv_sz _ _ _ _ _ _ _ HI) as Hsz.
      assert (Hc0 : cntW W0 (pre ++ [(φ c)]) = O).
      { apply cntW_notS. intros F.
        destruct (iv_child _ _ _ _ _ _ _ HI n c Hn Hc26) as [_ Hz0].
        apply (Hz0 Et). rewrite Hln. apply SW_snoc_iff. left. exact F. }
      pose proof (ins_step_new T cnt endv sz lbl W0 pre (φ c) n c HI Hn Hln eq_refl Hc26 Et Hszc)
        as HI'.
      rewrite <- Hfs, <- Hti in HI'.
      destruct (IH _ Hdec (i + 1) _ _ endv _ sz (s + 1) _ _ eq_refl ltac:(lia) HI'
                  ltac:(rewrite alength_set; exact Hcap) ltac:(sia)
                  ltac:(cbv beta; rewrite eqb_refl, Hti, Hfs; reflexivity)
                  ltac:(rewrite Hti, Hss, Hc0, add_spec; change (φ 1) with 1%Z;
                        rewrite Hs, Z.mod_small; rewrite ?wB_val; lia)
                  r Hr) as [Hlen Hrest].
      split; [rewrite Hlen, alength_set; reflexivity | exact Hrest].
    + apply eqb_false_spec in Et.
      destruct (ins_step_old T cnt endv sz lbl W0 pre (φ c) n c HI HW Hn Hln eq_refl Hc26 Et)
        as [HI' [Hk [Hmsz Hlm]]].
      rewrite <- Hfs, <- Hti in HI'.
      destruct (IH _ Hdec (i + 1) _ _ endv sz (tget T c n) (s + (cnt.[tget T c n] + 1)) _ _ eq_refl ltac:(lia) HI'
                  ltac:(rewrite alength_set; exact Hcap) Hmsz
                  ltac:(rewrite Hti, Hfs; exact Hlm)
                  ltac:(rewrite Hti, Hss, add_spec, Hk, Hs, Z.mod_small; rewrite ?wB_val; lia)
                  r Hr) as [Hlen Hrest].
      split; [rewrite Hlen, alength_set; reflexivity | exact Hrest].
  - rewrite <- Bool.not_true_iff_false, ltb_spec in Hi'.
    assert (Hiu : Z.to_nat (φ i) = List.length u) by lia.
    rewrite Hiu, firstn_all in HI, Hln. rewrite Hiu in Hs.
    subst r. simpl. split; [reflexivity|]. exists lbl. auto.
Qed.

(* ------------------------------------------------------------------ *)
(* The database loop                                                   *)
(* ------------------------------------------------------------------ *)

(* the array of words db is read as the list D of letter-index lists *)
Definition dbrep (db : array PrimString.string) (D : list (list Z)) : Prop :=
  (φ (PArray.length db)) = Z.of_nat (List.length D) /\
  forall j : int, ((φ j) < (φ (PArray.length db)))%Z ->
    exists u, nth_error D (Z.to_nat (φ j)) = Some u /\ wrep db.[j] u.

Lemma sumlen_firstn_le : forall D k, (sumlen (firstn k D) <= sumlen D)%nat.
Proof.
  intros D k. rewrite <- (firstn_skipn k D) at 2. unfold sumlen.
  rewrite map_app, list_sum_app. lia.
Qed.

Lemma stepsum_pathsum : forall W0 u, pathsum (W0 ++ [u]) u = stepsum W0 u (List.length u).
Proof.
  intros W0 u. unfold pathsum, stepsum. apply sumn_ext. intros l _.
  rewrite cntW_app, preb_firstn. lia.
Qed.

Lemma notin_prefix : forall (D : list (list Z)) j u, NoDup D -> nth_error D j = Some u ->
  ~ In u (firstn j D).
Proof.
  intros D j u HD Hu Hin.
  assert (E : D = firstn j D ++ u :: skipn (S j) D).
  { rewrite <- (firstn_skipn (S j) D) at 1. rewrite (firstn_snoc D j u Hu), <- app_assoc.
    reflexivity. }
  rewrite E in HD. apply NoDup_remove_2 in HD. apply HD. apply in_app_iff. left. exact Hin.
Qed.

Lemma build_spec : forall db D, dbrep db D -> NoDup D ->
  (Z.of_nat (List.length D) <= 30000)%Z ->
  Forall (fun u => Z.of_nat (List.length u) < 30)%Z D ->
  forall z j T cnt endv sz lbl (H : Acc (Zwf 0) (gap (PArray.length db) j)),
  gap (PArray.length db) j = z ->
  ((φ j) <= (φ (PArray.length db)))%Z ->
  Inv T cnt endv sz lbl (firstn (Z.to_nat (φ j)) D) (firstn (Z.to_nat (φ j)) D) ->
  (1 + Z.of_nat (sumlen D) <= (φ (PArray.length cnt)))%Z ->
  forall b, b = build db (PArray.length db) T cnt endv sz j H ->
  exists sz' lbl', Inv (b_T b) (b_cnt b) (b_end b) sz' lbl' D D.
Proof.
  intros db D Hdb HND HDl HDu z.
  induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros j T cnt endv sz lbl H Hz Hj HI Hcap b Hb.
  rewrite build_eq in Hb.
  pose proof Hdb as [Hdl Hdc].
  pose proof (to_Z_bounded j) as Bj.
  destruct (bdec (j <? PArray.length db)) as [Hj' | Hj'].
  - pose proof Hj' as Hlt. rewrite ltb_spec in Hlt.
    destruct (Hdc j Hlt) as [u [Hu Hw]].
    cbv zeta in Hb.
    set (W0 := firstn (Z.to_nat (φ j)) D) in *.
    assert (HW0 : Z.of_nat (List.length W0) = (φ j))
      by (unfold W0; rewrite length_firstn; lia).
    assert (Hul : (Z.of_nat (List.length u) < 30)%Z).
    { rewrite Forall_forall in HDu. apply HDu. eapply nth_error_In. exact Hu. }
    assert (HI0 : Inv T cnt endv sz lbl (W0 ++ [firstn (Z.to_nat (φ 0)) u]) W0)
      by (apply Inv_nil; exact HI).
    assert (Hfs : firstn (S (Z.to_nat (φ j))) D = W0 ++ [u]) by (apply firstn_snoc; exact Hu).
    assert (Hcap' : (1 + Z.of_nat (sumlen (W0 ++ [u])) <= (φ (PArray.length cnt)))%Z).
    { rewrite <- Hfs. pose proof (sumlen_firstn_le D (S (Z.to_nat (φ j)))). lia. }
    pose proof (iv_sz _ _ _ _ _ _ _ HI) as Hsz.
    destruct (ins_spec db.[j] u W0 Hw Hul ltac:(lia) _ 0 T cnt endv sz 0 0 lbl
                (Zwf_well_founded 0 (gap (PrimString.length db.[j]) 0)) eq_refl
                ltac:(destruct Hw as [Hwl _]; change (φ 0) with 0%Z; lia) HI0 Hcap'
                ltac:(change (φ 0) with 0%Z; lia)
                ltac:(rewrite (iv_root _ _ _ _ _ _ _ HI); reflexivity)
                ltac:(reflexivity) _ eq_refl)
      as [Hlen [lbl' [HI' [Hn' [Hln' Hs']]]]].
    assert (Hnin : ~ In u W0) by (apply notin_prefix; assumption).
    assert (Bs : (Z.of_nat (stepsum W0 u (List.length u)) <= 900030)%Z).
    { pose proof (stepsum_bound W0 u (List.length u)) as Bs.
      apply Nat2Z.inj_le in Bs. rewrite Nat2Z.inj_mul in Bs. nia. }
    match type of Hs' with (φ (r_s ?t)) = _ => set (r := t) in * end.
    assert (Hv : (φ (j + 1 + r_s r)) = EW (W0 ++ [u]) u).
    { rewrite EW_app_last by exact Hnin. rewrite stepsum_pathsum.
      rewrite !add_spec. change (φ 1) with 1%Z. rewrite Hs', wB_val.
      rewrite (Z.mod_small ((φ j) + 1)) by lia. rewrite Z.mod_small by lia. lia. }
    pose proof (Inv_end _ _ _ _ _ _ _ _ _ _ HI' Hn' Hln' Hnin Hv) as HI2.
    rewrite <- Hfs in HI2.
    assert (Hj1 : (φ (j + 1)) = ((φ j) + 1)%Z) by sia.
    assert (Htj : Z.to_nat (φ (j + 1)) = S (Z.to_nat (φ j))) by lia.
    rewrite <- Htj in HI2.
    assert (Hdec : Zwf 0 (gap (PArray.length db) (j + 1)) z)
      by (rewrite <- Hz; apply dec_step; exact Hj').
    exact (IH _ Hdec (j + 1) _ _ _ _ _ _ eq_refl ltac:(lia) HI2
             ltac:(rewrite Hlen; exact Hcap) b Hb).
  - rewrite <- Bool.not_true_iff_false, ltb_spec in Hj'.
    assert (HjD : Z.to_nat (φ j) = List.length D) by lia.
    rewrite HjD, firstn_all in HI. subst b. simpl. exists sz, lbl. exact HI.
Qed.

(* ------------------------------------------------------------------ *)
(* The query walk                                                      *)
(* ------------------------------------------------------------------ *)

Lemma sumn_tail_zero : forall f k n, (k <= n)%nat ->
  (forall l, (k <= l < n)%nat -> f l = O) -> sumn f n = sumn f k.
Proof.
  intros f k n. induction n as [|n IH]; intros Hk H.
  - replace k with O by lia. reflexivity.
  - destruct (Nat.eq_dec k (S n)) as [-> | Hne]; [reflexivity|].
    simpl. rewrite IH; [| lia | intros; apply H; lia]. rewrite H by lia. lia.
Qed.

Lemma qwalk_spec : forall T cnt endv sz lbl D, Inv T cnt endv sz lbl D D ->
  (Z.of_nat (List.length D) <= 30000)%Z ->
  forall q v N, wrep q v -> (Z.of_nat (List.length v) < 30)%Z ->
  (φ N) = Z.of_nat (List.length D) ->
  forall z i n s (H : Acc (Zwf 0) (gap (PrimString.length q) i)),
  gap (PrimString.length q) i = z -> ((φ i) <= (φ (PrimString.length q)))%Z ->
  ((φ n) < (φ sz))%Z -> lbl n = firstn (Z.to_nat (φ i)) v ->
  (φ s) = Z.of_nat (sumn (fun l => cntW D (firstn (S l) v)) (Z.to_nat (φ i))) ->
  (φ (qwalk q (PrimString.length q) T cnt endv N i n s H)) = Z.of_nat (ansm D v).
Proof.
  intros T cnt endv sz lbl D HI HD q v N Hw Hv HN z.
  induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros i n s H Hz Hi Hn Hln Hs.
  rewrite qwalk_eq.
  pose proof Hw as [Hwl Hwc].
  pose proof (to_Z_bounded i) as Bi.
  set (f := fun l => cntW D (firstn (S l) v)) in *.
  assert (Bf : forall k, (k <= List.length v)%nat -> (Z.of_nat (sumn f k) <= 900000)%Z).
  { intros k Hk. pose proof (sumn_le f k (List.length D) ltac:(intros; apply cntW_le)) as B.
    apply Nat2Z.inj_le in B. rewrite Nat2Z.inj_mul in B. nia. }
  assert (Hpath : pathsum D v = sumn f (List.length v)) by reflexivity.
  destruct (bdec (i <? PrimString.length q)) as [Hi' | Hi'].
  - pose proof Hi' as Hlt. rewrite ltb_spec in Hlt.
    destruct (Hwc i Hlt) as [Hx Hc26].
    cbv zeta.
    set (c := PrimString.get q i - 97) in *.
    assert (Hfs : firstn (S (Z.to_nat (φ i))) v = firstn (Z.to_nat (φ i)) v ++ [(φ c)])
      by (apply firstn_snoc; exact Hx).
    destruct (iv_child _ _ _ _ _ _ _ HI n c Hn Hc26) as [Hy Hz0].
    rewrite Hln, <- Hfs in Hy, Hz0.
    destruct (tget T c n =? 0) eqn:Et.
    + apply eqb_spec in Et. specialize (Hz0 Et).
      assert (Hnone : index_of v D = None).
      { apply index_of_none. intros Hin. apply Hz0. right. exists v.
        split; [exact Hin | apply preb_firstn]. }
      unfold ansm. rewrite Hnone, Hpath.
      assert (Hrest : sumn f (List.length v) = sumn f (Z.to_nat (φ i))).
      { apply sumn_tail_zero; [lia|]. intros l Hl. unfold f. apply cntW_notS.
        intros HS. apply Hz0. eapply SW_closed; [|exact HS].
        replace (firstn (S (Z.to_nat (φ i))) v)
          with (firstn (S (Z.to_nat (φ i))) (firstn (S l) v))
          by (rewrite firstn_firstn; f_equal; lia).
        apply preb_firstn. }
      pose proof (Bf (Z.to_nat (φ i)) ltac:(lia)).
      rewrite Hrest, add_spec, HN, Hs, wB_val, Z.mod_small by lia. lia.
    + apply eqb_false_spec in Et. destruct (Hy Et) as [Hmsz Hlm].
      assert (Hmpos : (0 < (φ (tget T c n)))%Z).
      { pose proof (to_Z_bounded (tget T c n)).
        destruct (Z.eq_dec (φ (tget T c n)) 0) as [E|E]; [|lia].
        exfalso. apply Et. apply to_Z_inj. exact E. }
      assert (Hi1 : (φ (i + 1)) = ((φ i) + 1)%Z) by sia.
      assert (Hti : Z.to_nat (φ (i + 1)) = S (Z.to_nat (φ i))) by lia.
      assert (Hdec : Zwf 0 (gap (PrimString.length q) (i + 1)) z)
        by (rewrite <- Hz; apply dec_step; exact Hi').
      pose proof (iv_cnt _ _ _ _ _ _ _ HI (tget T c n) ltac:(lia)) as Hcm.
      rewrite Hlm in Hcm.
      pose proof (Bf (S (Z.to_nat (φ i))) ltac:(lia)) as Bf1.
      apply (IH _ Hdec (i + 1) _ _ _ eq_refl ltac:(lia) Hmsz ltac:(rewrite Hti; exact Hlm)).
      rewrite Hti, add_spec, Hs, Hcm, Z.mod_small.
      * change (sumn f (S (Z.to_nat (φ i))))
          with (sumn f (Z.to_nat (φ i)) + f (Z.to_nat (φ i)))%nat.
        rewrite Nat2Z.inj_add. reflexivity.
      * change (sumn f (S (Z.to_nat (φ i))))
          with (sumn f (Z.to_nat (φ i)) + f (Z.to_nat (φ i)))%nat in Bf1.
        rewrite Nat2Z.inj_add in Bf1.
        change (f (Z.to_nat (φ i))) with (cntW D (firstn (S (Z.to_nat (φ i))) v)) in Bf1.
        rewrite wB_val. lia.
  - rewrite <- Bool.not_true_iff_false, ltb_spec in Hi'.
    assert (Hiv : Z.to_nat (φ i) = List.length v) by lia.
    rewrite Hiv, firstn_all in Hln. rewrite Hiv in Hs.
    cbv zeta.
    pose proof (iv_end _ _ _ _ _ _ _ HI n Hn) as He. rewrite Hln in He.
    unfold EW in He. unfold ansm.
    destruct (index_of v D) as [k|] eqn:Ei.
    + replace (endv.[n] =? 0) with false.
      * exact He.
      * symmetry. apply eqb_false_spec. intros F. rewrite F in He.
        change (φ 0) with 0%Z in He. lia.
    + replace (endv.[n] =? 0) with true.
      * pose proof (Bf (List.length v) ltac:(lia)).
        rewrite add_spec, HN, Hs, wB_val, Z.mod_small by lia. rewrite <- Hpath. lia.
      * symmetry. apply eqb_spec. apply to_Z_inj. exact He.
Qed.

Lemma query_spec : forall T cnt endv sz lbl D, Inv T cnt endv sz lbl D D ->
  (Z.of_nat (List.length D) <= 30000)%Z ->
  forall q v N, wrep q v -> (Z.of_nat (List.length v) < 30)%Z ->
  (φ N) = Z.of_nat (List.length D) ->
  (φ (query q T cnt endv N)) = Z.of_nat (ansm D v).
Proof.
  intros T cnt endv sz lbl D HI HD q v N Hw Hv HN. unfold query.
  pose proof (iv_sz _ _ _ _ _ _ _ HI) as Hsz.
  pose proof Hw as [Hwl _].
  apply (qwalk_spec T cnt endv sz lbl D HI HD q v N Hw Hv HN _ 0 0 0 _ eq_refl).
  - change (φ 0) with 0%Z. lia.
  - change (φ 0) with 0%Z. lia.
  - rewrite (iv_root _ _ _ _ _ _ _ HI). reflexivity.
  - reflexivity.
Qed.

Lemma answer_spec : forall T cnt endv sz lbl D, Inv T cnt endv sz lbl D D ->
  (Z.of_nat (List.length D) <= 30000)%Z ->
  forall qs Qs N, dbrep qs Qs -> Forall (fun v => Z.of_nat (List.length v) < 30)%Z Qs ->
  (φ N) = Z.of_nat (List.length D) ->
  forall z k out (H : Acc (Zwf 0) (gap (PArray.length qs) k)),
  gap (PArray.length qs) k = z -> ((φ k) <= (φ (PArray.length qs)))%Z ->
  PArray.length out = PArray.length qs ->
  (forall k', ((φ k') < (φ k))%Z -> forall v, nth_error Qs (Z.to_nat (φ k')) = Some v ->
      (φ (out.[k'])) = Z.of_nat (ansm D v)) ->
  forall res, res = answer qs (PArray.length qs) T cnt endv N out k H ->
  PArray.length res = PArray.length qs /\
  forall k', ((φ k') < (φ (PArray.length qs)))%Z ->
    forall v, nth_error Qs (Z.to_nat (φ k')) = Some v ->
      (φ (res.[k'])) = Z.of_nat (ansm D v).
Proof.
  intros T cnt endv sz lbl D HI HD qs Qs N Hqs HQ HN z.
  induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros k out H Hz Hk Hlen Hout res Hres.
  rewrite answer_eq in Hres.
  pose proof Hqs as [Hql Hqc].
  destruct (bdec (k <? PArray.length qs)) as [Hk' | Hk'].
  - pose proof Hk' as Hlt. rewrite ltb_spec in Hlt.
    destruct (Hqc k Hlt) as [v [Hv Hw]].
    assert (Hvl : (Z.of_nat (List.length v) < 30)%Z).
    { rewrite Forall_forall in HQ. apply HQ. eapply nth_error_In. exact Hv. }
    assert (Hk1 : (φ (k + 1)) = ((φ k) + 1)%Z) by sia.
    assert (Hdec : Zwf 0 (gap (PArray.length qs) (k + 1)) z)
      by (rewrite <- Hz; apply dec_step; exact Hk').
    apply (IH _ Hdec (k + 1) (out.[k <- query qs.[k] T cnt endv N])
             (Acc_inv H (dec_step (PArray.length qs) k Hk')) eq_refl ltac:(lia)
             ltac:(rewrite alength_set; exact Hlen)); [|exact Hres].
    intros k' Hk'' v' Hv'.
    destruct (Z.eq_dec (φ k') (φ k)) as [E | E].
    + assert (k' = k) by (apply to_Z_inj; exact E). subst k'.
      rewrite aget_set_same by lia. rewrite Hv in Hv'. injection Hv' as <-.
      exact (query_spec T cnt endv sz lbl D HI HD _ v N Hw Hvl HN).
    + rewrite aget_set_other by (intros F; apply E; rewrite F; reflexivity).
      apply Hout; [lia | exact Hv'].
  - rewrite <- Bool.not_true_iff_false, ltb_spec in Hk'.
    subst res. split; [exact Hlen|]. intros k' Hk'' v Hv. apply Hout; [lia | exact Hv].
Qed.

(* ------------------------------------------------------------------ *)
(* The total length and the initial trie                               *)
(* ------------------------------------------------------------------ *)

Lemma skipn_nth : forall {A} (D : list A) j u, nth_error D j = Some u ->
  skipn j D = u :: skipn (S j) D.
Proof.
  intros A D. induction D as [|y D IH]; intros j u H; [destruct j; discriminate|].
  destruct j as [|j]; simpl in H.
  - injection H as ->. reflexivity.
  - simpl. apply IH. exact H.
Qed.

Lemma sumlen_cons : forall u W, sumlen (u :: W) = (List.length u + sumlen W)%nat.
Proof. reflexivity. Qed.

Lemma total_spec : forall db D, dbrep db D ->
  forall z j acc (H : Acc (Zwf 0) (gap (PArray.length db) j)),
  gap (PArray.length db) j = z -> ((φ j) <= (φ (PArray.length db)))%Z ->
  ((φ acc) + Z.of_nat (sumlen (skipn (Z.to_nat (φ j)) D)) < wB)%Z ->
  (φ (total db (PArray.length db) j acc H))
  = ((φ acc) + Z.of_nat (sumlen (skipn (Z.to_nat (φ j)) D)))%Z.
Proof.
  intros db D Hdb z.
  induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros j acc H Hz Hj Hb.
  rewrite total_eq.
  pose proof Hdb as [Hdl Hdc].
  pose proof (to_Z_bounded j) as Bj.
  destruct (bdec (j <? PArray.length db)) as [Hj' | Hj'].
  - pose proof Hj' as Hlt. rewrite ltb_spec in Hlt.
    destruct (Hdc j Hlt) as [u [Hu [Hwl _]]].
    rewrite (skipn_nth D _ u Hu), sumlen_cons in *.
    assert (Hj1 : (φ (j + 1)) = ((φ j) + 1)%Z) by sia.
    assert (Htj : Z.to_nat (φ (j + 1)) = S (Z.to_nat (φ j))) by lia.
    assert (Hdec : Zwf 0 (gap (PArray.length db) (j + 1)) z)
      by (rewrite <- Hz; apply dec_step; exact Hj').
    pose proof (to_Z_bounded acc).
    assert (Ha : (φ (acc + PrimString.length db.[j])) = ((φ acc) + Z.of_nat (List.length u))%Z).
    { rewrite add_spec, Hwl. apply Z.mod_small. lia. }
    rewrite (IH _ Hdec (j + 1) _ _ eq_refl ltac:(lia)); rewrite Ha, Htj; lia.
  - rewrite <- Bool.not_true_iff_false, ltb_spec in Hj'.
    rewrite skipn_all2 by lia. simpl. lia.
Qed.

Lemma sumlen_bound : forall D, Forall (fun u => Z.of_nat (List.length u) < 30)%Z D ->
  (Z.of_nat (sumlen D) <= 29 * Z.of_nat (List.length D))%Z.
Proof.
  induction D as [|u D IH]; intros H; [simpl; lia|].
  inversion H as [|? ? Hu HD]; subst. rewrite sumlen_cons. specialize (IH HD).
  simpl List.length. lia.
Qed.

Lemma Inv_init : forall cap : int, (1 <= (φ cap) <= 4194303)%Z ->
  Inv (mk_tab cap) (PArray.make cap 0) (PArray.make cap 0) 1 (fun _ => []) [] [].
Proof.
  intros cap Hcap.
  assert (Hl : PArray.length (PArray.make cap 0) = cap) by (apply alength_make; lia).
  assert (Hlt1 : forall n : int, ((φ n) < (φ 1))%Z -> n = 0).
  { intros n Hn. change (φ 1) with 1%Z in Hn. pose proof (to_Z_bounded n).
    apply to_Z_inj. change (φ 0) with 0%Z. lia. }
  assert (Hg : forall c n, tget (mk_tab cap) c n = 0).
  { intros c n. unfold tget. rewrite sel_mk_tab. apply aget_make. }
  constructor.
  - intros c _. rewrite sel_mk_tab. reflexivity.
  - reflexivity.
  - rewrite Hl. change (φ 1) with 1%Z. lia.
  - change (φ 1) with 1%Z. simpl. lia.
  - reflexivity.
  - intros n m Hn Hm _. rewrite (Hlt1 n Hn), (Hlt1 m Hm). reflexivity.
  - intros n _. left. reflexivity.
  - intros n c _ _. rewrite Hg. split; [intros F; contradiction F; reflexivity|].
    intros _ [F | [v [[] _]]]. discriminate.
  - intros n c _ _. rewrite Hg, aget_make. split; reflexivity.
  - intros n Hn. change (φ 1) with 1%Z in Hn. lia.
  - intros n _. rewrite aget_make. reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* Strings: a word is read as its letter indices                       *)
(* ------------------------------------------------------------------ *)

Definition lw (w : String.string) : list Z :=
  map (fun a => (Z.of_N (Ascii.N_of_ascii a) - 97)%Z) (String.list_ascii_of_string w).

Lemma lw_length : forall w, List.length (lw w) = String.length w.
Proof. induction w as [|a w IH]; simpl; [reflexivity | rewrite <- IH; reflexivity]. Qed.

Lemma lw_get : forall w k c, String.get k w = Some c ->
  nth_error (lw w) k = Some (Z.of_N (Ascii.N_of_ascii c) - 97)%Z.
Proof.
  induction w as [|a w IH]; intros k c H; [discriminate|].
  destruct k as [|k]; simpl in H.
  - injection H as ->. reflexivity.
  - simpl. apply IH. exact H.
Qed.

Lemma ascii_Z_inj : forall a b : Ascii.ascii,
  (Z.of_N (Ascii.N_of_ascii a) - 97 = Z.of_N (Ascii.N_of_ascii b) - 97)%Z -> a = b.
Proof.
  intros a b H. rewrite <- (Ascii.ascii_N_embedding a), <- (Ascii.ascii_N_embedding b).
  f_equal. lia.
Qed.

Lemma lw_inj : forall a b, lw a = lw b -> a = b.
Proof.
  induction a as [|x a IH]; intros [|y b] H; try discriminate; [reflexivity|].
  simpl in H. injection H as H1 H2. apply ascii_Z_inj in H1. subst y.
  f_equal. apply IH. exact H2.
Qed.

Lemma NoDup_map_lw : forall l, NoDup l -> NoDup (map lw l).
Proof.
  induction l as [|a l IH]; intros H; simpl; [constructor|].
  inversion H as [|? ? Ha Hl]; subst. constructor; [|apply IH; exact Hl].
  intros Hin. apply in_map_iff in Hin as [b [Eb Hb]]. apply lw_inj in Eb. subst b.
  contradiction.
Qed.

Lemma wrep_of_repr : forall (x : PrimString.string) (w : String.string),
  repr x w -> lowercase w -> wrep x (lw w).
Proof.
  intros x w [Hl Hc] Hlow. split.
  - rewrite lw_length. symmetry. exact Hl.
  - intros i Hi. pose proof (to_Z_bounded i) as Bi.
    destruct (Hc (Z.to_nat (φ i)) ltac:(lia)) as [c [Hget Hrep]].
    unfold repr, repr_uint in Hrep.
    assert (Ei : Uint63.of_nat (Z.to_nat (φ i)) = i).
    { apply to_Z_inj. rewrite of_Z_spec. rewrite Z2Nat.id by lia. apply Z.mod_small. lia. }
    rewrite Ei in Hrep.
    pose proof (Hlow _ _ Hget) as Hc97.
    set (g := PrimString.get x i) in *.
    pose proof (to_Z_bounded g) as Bg.
    assert (Hg : (φ g) = Z.of_N (Ascii.N_of_ascii c)) by (rewrite <- Hrep; lia).
    assert (Hg97 : (φ (g - 97)) = ((φ g) - 97)%Z).
    { rewrite sub_spec. change (φ 97) with 97%Z. apply Z.mod_small. lia. }
    rewrite Hg97, Hg. split; [apply lw_get; exact Hget | lia].
Qed.

Lemma dbrep_of_repr : forall (x : array PrimString.string) (db : list String.string),
  repr x db -> Forall lowercase db -> dbrep x (map lw db).
Proof.
  intros x db [Hl Hc] Hlow. rewrite Forall_forall in Hlow. split.
  - rewrite length_map. symmetry. exact Hl.
  - intros j Hj. pose proof (to_Z_bounded j) as Bj.
    assert (Hj' : (Z.to_nat (φ j) < List.length db)%nat).
    { assert (Hj2 : ((φ j) < Z.of_nat (List.length db))%Z) by (rewrite Hl; exact Hj). lia. }
    destruct (Hc (Z.to_nat (φ j)) Hj') as [m [Hm Hrep]].
    assert (Ej : Uint63.of_nat (Z.to_nat (φ j)) = j).
    { apply to_Z_inj. rewrite of_Z_spec. rewrite Z2Nat.id by lia. apply Z.mod_small. lia. }
    rewrite Ej in Hrep.
    exists (lw m). split; [rewrite nth_error_map, Hm; reflexivity|].
    apply wrep_of_repr; [exact Hrep | apply Hlow; eapply nth_error_In; exact Hm].
Qed.

(* ------------------------------------------------------------------ *)
(* Longest common prefixes                                             *)
(* ------------------------------------------------------------------ *)

Fixpoint lcpl (a b : list Z) : nat :=
  match a, b with
  | x :: a', y :: b' => if Z.eqb x y then S (lcpl a' b') else O
  | _, _ => O
  end.

Fixpoint lcpS (a b : String.string) : nat :=
  match a, b with
  | String.String x a', String.String y b' =>
      if Ascii.ascii_dec x y then S (lcpS a' b') else O
  | _, _ => O
  end.

Lemma lcpl_lw : forall a b, lcpl (lw a) (lw b) = lcpS a b.
Proof.
  induction a as [|x a IH]; intros [|y b]; try reflexivity.
  simpl. destruct (Ascii.ascii_dec x y) as [-> | Hne].
  - rewrite Z.eqb_refl. f_equal. apply IH.
  - destruct (Z.eqb_spec (Z.of_N (Ascii.N_of_ascii x) - 97) (Z.of_N (Ascii.N_of_ascii y) - 97))
      as [E | E]; [|reflexivity].
    apply ascii_Z_inj in E. contradiction.
Qed.

Lemma starts_with_empty : forall q, starts_with String.EmptyString q -> q = String.EmptyString.
Proof. intros [|a q] [s Hs]; [reflexivity | discriminate]. Qed.

Lemma starts_with_cons : forall x a z q,
  starts_with (String.String x a) (String.String z q) -> z = x /\ starts_with a q.
Proof. intros x a z q [s Hs]. simpl in Hs. injection Hs as -> ->. split; [reflexivity | exists s; reflexivity]. Qed.

Lemma lcp_length_lcpS : forall a b, lcp_length a b (N.of_nat (lcpS a b)).
Proof.
  induction a as [|x a IH]; intros b.
  - exists String.EmptyString. split; [exists String.EmptyString; reflexivity|].
    split; [exists b; reflexivity|]. split; [reflexivity|].
    intros q Hq _. apply starts_with_empty in Hq. subst q. unfold slen. simpl. lia.
  - destruct b as [|y b].
    + exists String.EmptyString. split; [exists (String.String x a); reflexivity|].
      split; [exists String.EmptyString; reflexivity|]. split; [reflexivity|].
      intros q _ Hq. apply starts_with_empty in Hq. subst q. unfold slen. simpl. lia.
    + simpl. destruct (Ascii.ascii_dec x y) as [<- | Hne].
      * destruct (IH b) as [p [[s1 Hs1] [[s2 Hs2] [Hp Hmax]]]].
        exists (String.String x p). split; [exists s1; simpl; rewrite <- Hs1; reflexivity|].
        split; [exists s2; simpl; rewrite <- Hs2; reflexivity|].
        split; [unfold slen in *; simpl; lia|].
        intros [|z q] Hqa Hqb; [unfold slen; simpl; lia|].
        apply starts_with_cons in Hqa as [_ Hqa]. apply starts_with_cons in Hqb as [_ Hqb].
        specialize (Hmax q Hqa Hqb). unfold slen in *. simpl. lia.
      * exists String.EmptyString. split; [exists (String.String x a); reflexivity|].
        split; [exists (String.String y b); reflexivity|]. split; [reflexivity|].
        intros [|z q] Hqa Hqb; [unfold slen; simpl; lia|].
        apply starts_with_cons in Hqa as [E1 _]. apply starts_with_cons in Hqb as [E2 _].
        congruence.
Qed.

Lemma sumn_zero : forall f n, (forall l, (l < n)%nat -> f l = O) -> sumn f n = O.
Proof.
  intros f n. induction n as [|n IH]; intros H; [reflexivity|].
  simpl. rewrite IH by (intros; apply H; lia). rewrite H by lia. reflexivity.
Qed.

Lemma sumn_add : forall f g n, sumn (fun l => f l + g l)%nat n = (sumn f n + sumn g n)%nat.
Proof. intros f g n. induction n as [|n IH]; [reflexivity|]. simpl. rewrite IH. lia. Qed.

Lemma sumn_shift : forall f n, sumn f (S n) = (f O + sumn (fun l => f (S l)) n)%nat.
Proof.
  intros f n. induction n as [|n IH]; [simpl; lia|].
  change (sumn f (S (S n))) with (sumn f (S n) + f (S n))%nat. rewrite IH. simpl. lia.
Qed.

Lemma sumn_lcpl : forall q v,
  sumn (fun l => if preb (firstn (S l) q) v then 1 else 0)%nat (List.length q) = lcpl q v.
Proof.
  induction q as [|x q IH]; intros v; [reflexivity|].
  cbn [List.length]. rewrite sumn_shift.
  destruct v as [|y v].
  - simpl. apply sumn_zero. intros l _. reflexivity.
  - cbn [lcpl firstn preb]. destruct (Z.eqb x y).
    + simpl. f_equal. apply IH.
    + simpl. apply sumn_zero. intros l _. reflexivity.
Qed.

Lemma pathsum_lcp : forall W q, pathsum W q = list_sum (map (lcpl q) W).
Proof.
  induction W as [|v W IH]; intros q.
  - unfold pathsum. apply sumn_zero. intros l _. reflexivity.
  - unfold pathsum in *. simpl map. simpl list_sum. rewrite <- IH.
    rewrite <- sumn_lcpl.
    rewrite <- sumn_add. apply sumn_ext. intros l _. rewrite cntW_cons. reflexivity.
Qed.

Lemma fold_N_sum : forall {A} (g : A -> nat) l,
  fold_right N.add 0%N (map (fun x => N.of_nat (g x)) l) = N.of_nat (list_sum (map g l)).
Proof. intros A g l. induction l as [|a l IH]; [reflexivity|]. simpl. rewrite IH. lia. Qed.

Lemma Forall2_map_r : forall {A B} (R : A -> B -> Prop) (f : A -> B) l,
  (forall x, In x l -> R x (f x)) -> Forall2 R l (map f l).
Proof.
  intros A B R f l. induction l as [|a l IH]; intros H; simpl; constructor.
  - apply H. left. reflexivity.
  - apply IH. intros x Hx. apply H. right. exact Hx.
Qed.

Lemma steps_ok : forall db w, search_steps db w (N.of_nat (ansm (map lw db) (lw w))).
Proof.
  intros db w. unfold ansm.
  assert (Hm : forall l, map (lcpl (lw w)) (map lw l) = map (lcpS w) l).
  { intros l. rewrite map_map. apply map_ext. intros a. apply lcpl_lw. }
  destruct (index_of (lw w) (map lw db)) as [k|] eqn:Ei.
  - apply index_of_some in Ei. rewrite nth_error_map in Ei.
    destruct (nth_error db k) as [w'|] eqn:Ek; [|discriminate].
    simpl in Ei. injection Ei as Ew. apply lw_inj in Ew. subst w'.
    exists (N.of_nat (S k)), (map (fun v => N.of_nat (lcpS w v)) (firstn (S k) db)).
    split; [|split].
    + left. exists (N.of_nat k). split; [rewrite Nat2N.id; exact Ek | lia].
    + rewrite Nat2N.id. apply Forall2_map_r. intros v _. apply lcp_length_lcpS.
    + rewrite fold_N_sum, pathsum_lcp, firstn_map, Hm. lia.
  - apply index_of_none in Ei.
    exists (len db), (map (fun v => N.of_nat (lcpS w v)) db).
    split; [|split].
    + right. split; [intros Hin; apply Ei; apply in_map; exact Hin | reflexivity].
    + unfold len. rewrite Nat2N.id, firstn_all. apply Forall2_map_r.
      intros v _. apply lcp_length_lcpS.
    + rewrite fold_N_sum, pathsum_lcp, Hm, length_map. unfold len. lia.
Qed.

(* ------------------------------------------------------------------ *)
(* The contract                                                        *)
(* ------------------------------------------------------------------ *)

Lemma lengths_ok : forall l : list String.string,
  Forall (fun w => slen w < 30)%N l ->
  Forall (fun u => Z.of_nat (List.length u) < 30)%Z (map lw l).
Proof.
  intros l H. apply Forall_map. eapply Forall_impl; [|exact H].
  intros w Hw. unfold slen in Hw. rewrite lw_length. lia.
Qed.

Lemma baza_impl_correct : forall (db qs : list String.string) (x y : array PrimString.string),
  valid_input db qs -> repr x db -> repr y qs ->
  exists o : list N, repr (baza_impl x y) o /\ baza_spec db qs o.
Proof.
  intros db qs x y Hv Hx Hy.
  destruct Hv as [Hn Hq Hdl Hql Hdlo Hqlo Hnd].
  unfold len in Hn, Hq.
  set (D := map lw db). set (Qs := map lw qs).
  assert (HdbD : dbrep x D) by (apply dbrep_of_repr; assumption).
  assert (HqsQ : dbrep y Qs) by (apply dbrep_of_repr; assumption).
  assert (HDl : (Z.of_nat (List.length D) <= 30000)%Z) by (unfold D; rewrite length_map; lia).
  assert (HDu := lengths_ok db Hdl). fold D in HDu.
  assert (HQu := lengths_ok qs Hql). fold Qs in HQu.
  assert (HND : NoDup D) by (apply NoDup_map_lw; exact Hnd).
  pose proof HdbD as [HN _]. pose proof HqsQ as [HQ _].
  pose proof (sumlen_bound D HDu) as Bsl.
  assert (Htot : (φ (total x (PArray.length x) 0 0 (Zwf_well_founded 0 (gap (PArray.length x) 0))))
                 = Z.of_nat (sumlen D)).
  { rewrite (total_spec x D HdbD _ 0 0 _ eq_refl); change (φ 0) with 0%Z;
      [reflexivity | lia | rewrite wB_val; simpl skipn; lia]. }
  set (cap := 1 + total x (PArray.length x) 0 0 (Zwf_well_founded 0 (gap (PArray.length x) 0))).
  assert (Hcap : (φ cap) = (1 + Z.of_nat (sumlen D))%Z).
  { unfold cap. rewrite add_spec, Htot. change (φ 1) with 1%Z. rewrite wB_val.
    apply Z.mod_small. lia. }
  pose proof (Inv_init cap ltac:(lia)) as HI0.
  assert (Hlc : PArray.length (PArray.make cap 0) = cap) by (apply alength_make; lia).
  destruct (build_spec x D HdbD HND HDl HDu _ 0 (mk_tab cap) (PArray.make cap 0)
              (PArray.make cap 0) 1 (fun _ => [])
              (Zwf_well_founded 0 (gap (PArray.length x) 0)) eq_refl
              ltac:(change (φ 0) with 0%Z; lia) HI0
              ltac:(rewrite Hlc; lia) _ eq_refl)
    as [sz' [lbl' HI]].
  set (b := build x (PArray.length x) (mk_tab cap) (PArray.make cap 0) (PArray.make cap 0) 1 0
              (Zwf_well_founded 0 (gap (PArray.length x) 0))) in HI.
  assert (HQl0 : (Z.of_nat (List.length Qs) <= 30000)%Z) by (unfold Qs; rewrite length_map; lia).
  assert (HQl : PArray.length (PArray.make (PArray.length y) 0) = PArray.length y)
    by (apply alength_make; lia).
  destruct (answer_spec (b_T b) (b_cnt b) (b_end b) sz' lbl' D HI HDl y Qs (PArray.length x)
              HqsQ HQu HN _ 0 (PArray.make (PArray.length y) 0)
              (Zwf_well_founded 0 (gap (PArray.length y) 0)) eq_refl
              ltac:(change (φ 0) with 0%Z; lia) HQl
              ltac:(intros k' Hk'; change (φ 0) with 0%Z in Hk'; pose proof (to_Z_bounded k'); lia)
              (baza_impl x y) eq_refl)
    as [Hrl Hrc].
  exists (map (fun q => N.of_nat (ansm D (lw q))) qs).
  split.
  - assert (Hyq : (φ (PArray.length y)) = Z.of_nat (List.length qs))
      by (unfold Qs in HQ; rewrite length_map in HQ; exact HQ).
    split.
    + rewrite length_map.
      assert (E : (φ (@PArray.length@{Set} int (baza_impl x y))) = Z.of_nat (List.length qs))
        by (rewrite Hrl; exact Hyq).
      symmetry. exact E.
    + intros k Hk. rewrite length_map in Hk.
      destruct (nth_error qs k) as [q|] eqn:Eq; [| apply nth_error_None in Eq; lia].
      exists (N.of_nat (ansm D (lw q))). split; [rewrite nth_error_map, Eq; reflexivity|].
      assert (Ek : (φ (Uint63.of_nat k)) = Z.of_nat k).
      { rewrite of_Z_spec. apply Z.mod_small. rewrite wB_val. lia. }
      pose proof (Hrc (Uint63.of_nat k) ltac:(lia) (lw q)
                    ltac:(rewrite Ek, Nat2Z.id; unfold Qs; rewrite nth_error_map, Eq; reflexivity))
        as Hc.
      assert (Hc' : Z.to_N (φ (@PArray.get@{Set} int (baza_impl x y) (Uint63.of_nat k)))
                    = N.of_nat (ansm D (lw q)))
        by (rewrite Hc; lia).
      exact Hc'.
  - unfold baza_spec. apply Forall2_map_r. intros w _. apply steps_ok.
Qed.

(* ------------------------------------------------------------------ *)
(* The spec's items, at top level                                      *)
(* ------------------------------------------------------------------ *)

Definition baza : array PrimString.string -> array PrimString.string -> array uint :=
  baza_impl.
Elpi complexity baza.

Definition baza_correct : forall (db qs : list String.string) (x y : array PrimString.string),
  valid_input db qs -> repr x db -> repr y qs ->
  exists o : list N, repr (baza x y) o /\ baza_spec db qs o
  := baza_impl_correct.

(* ------------------------------------------------------------------ *)
(* Cost                                                                *)
(* ------------------------------------------------------------------ *)

(* The cost translations are next to the definitions (Elpi complexity on
   sumbool, bdec, the record tab and its 26 projections, sel, upd, mk_tab,
   tget, tset, ires/bres and their projections, ins_loop, build, qwalk,
   query, answer, total, baza_impl, baza).  Per-call bounds: the projections
   2 steps, sel 30, upd 200, tget 40, tset 300, mk_tab 200, bdec 2; per
   loop (induction on a nat bound of the Acc measure gap):
     ins_loop, qwalk from i : gap L i * 500 + 20 (+ 30)
     total from j            : gap N j * 50 + 20
     query q                 : size q * 500 + 60
     build, answer from j    : ssum (sizes of the cells j..) * 500
                               + gap * 300 (resp. 200) + 20
   baza_impl : 500 * (sizes db + sizes qs) + 400 * |db| + 200 * |qs| + 1000,
   within baza_time's 500 * (sizes db + sizes qs + |db| + |qs| + 1) + 1000. *)

From Stdlib Require Import ssreflect.

Lemma tc0_time t tC : (cost (tc0_cost stepsCM t tC) <= 2)%nat.
Proof. destruct tC. unfold tc0_cost. cbn. lia. Qed.
Lemma tc1_time t tC : (cost (tc1_cost stepsCM t tC) <= 2)%nat.
Proof. destruct tC. unfold tc1_cost. cbn. lia. Qed.
Lemma tc2_time t tC : (cost (tc2_cost stepsCM t tC) <= 2)%nat.
Proof. destruct tC. unfold tc2_cost. cbn. lia. Qed.
Lemma tc3_time t tC : (cost (tc3_cost stepsCM t tC) <= 2)%nat.
Proof. destruct tC. unfold tc3_cost. cbn. lia. Qed.
Lemma tc4_time t tC : (cost (tc4_cost stepsCM t tC) <= 2)%nat.
Proof. destruct tC. unfold tc4_cost. cbn. lia. Qed.
Lemma tc5_time t tC : (cost (tc5_cost stepsCM t tC) <= 2)%nat.
Proof. destruct tC. unfold tc5_cost. cbn. lia. Qed.
Lemma tc6_time t tC : (cost (tc6_cost stepsCM t tC) <= 2)%nat.
Proof. destruct tC. unfold tc6_cost. cbn. lia. Qed.
Lemma tc7_time t tC : (cost (tc7_cost stepsCM t tC) <= 2)%nat.
Proof. destruct tC. unfold tc7_cost. cbn. lia. Qed.
Lemma tc8_time t tC : (cost (tc8_cost stepsCM t tC) <= 2)%nat.
Proof. destruct tC. unfold tc8_cost. cbn. lia. Qed.
Lemma tc9_time t tC : (cost (tc9_cost stepsCM t tC) <= 2)%nat.
Proof. destruct tC. unfold tc9_cost. cbn. lia. Qed.
Lemma tc10_time t tC : (cost (tc10_cost stepsCM t tC) <= 2)%nat.
Proof. destruct tC. unfold tc10_cost. cbn. lia. Qed.
Lemma tc11_time t tC : (cost (tc11_cost stepsCM t tC) <= 2)%nat.
Proof. destruct tC. unfold tc11_cost. cbn. lia. Qed.
Lemma tc12_time t tC : (cost (tc12_cost stepsCM t tC) <= 2)%nat.
Proof. destruct tC. unfold tc12_cost. cbn. lia. Qed.
Lemma tc13_time t tC : (cost (tc13_cost stepsCM t tC) <= 2)%nat.
Proof. destruct tC. unfold tc13_cost. cbn. lia. Qed.
Lemma tc14_time t tC : (cost (tc14_cost stepsCM t tC) <= 2)%nat.
Proof. destruct tC. unfold tc14_cost. cbn. lia. Qed.
Lemma tc15_time t tC : (cost (tc15_cost stepsCM t tC) <= 2)%nat.
Proof. destruct tC. unfold tc15_cost. cbn. lia. Qed.
Lemma tc16_time t tC : (cost (tc16_cost stepsCM t tC) <= 2)%nat.
Proof. destruct tC. unfold tc16_cost. cbn. lia. Qed.
Lemma tc17_time t tC : (cost (tc17_cost stepsCM t tC) <= 2)%nat.
Proof. destruct tC. unfold tc17_cost. cbn. lia. Qed.
Lemma tc18_time t tC : (cost (tc18_cost stepsCM t tC) <= 2)%nat.
Proof. destruct tC. unfold tc18_cost. cbn. lia. Qed.
Lemma tc19_time t tC : (cost (tc19_cost stepsCM t tC) <= 2)%nat.
Proof. destruct tC. unfold tc19_cost. cbn. lia. Qed.
Lemma tc20_time t tC : (cost (tc20_cost stepsCM t tC) <= 2)%nat.
Proof. destruct tC. unfold tc20_cost. cbn. lia. Qed.
Lemma tc21_time t tC : (cost (tc21_cost stepsCM t tC) <= 2)%nat.
Proof. destruct tC. unfold tc21_cost. cbn. lia. Qed.
Lemma tc22_time t tC : (cost (tc22_cost stepsCM t tC) <= 2)%nat.
Proof. destruct tC. unfold tc22_cost. cbn. lia. Qed.
Lemma tc23_time t tC : (cost (tc23_cost stepsCM t tC) <= 2)%nat.
Proof. destruct tC. unfold tc23_cost. cbn. lia. Qed.
Lemma tc24_time t tC : (cost (tc24_cost stepsCM t tC) <= 2)%nat.
Proof. destruct tC. unfold tc24_cost. cbn. lia. Qed.
Lemma tc25_time t tC : (cost (tc25_cost stepsCM t tC) <= 2)%nat.
Proof. destruct tC. unfold tc25_cost. cbn. lia. Qed.
Arguments tc0_cost : simpl never.
Arguments tc1_cost : simpl never.
Arguments tc2_cost : simpl never.
Arguments tc3_cost : simpl never.
Arguments tc4_cost : simpl never.
Arguments tc5_cost : simpl never.
Arguments tc6_cost : simpl never.
Arguments tc7_cost : simpl never.
Arguments tc8_cost : simpl never.
Arguments tc9_cost : simpl never.
Arguments tc10_cost : simpl never.
Arguments tc11_cost : simpl never.
Arguments tc12_cost : simpl never.
Arguments tc13_cost : simpl never.
Arguments tc14_cost : simpl never.
Arguments tc15_cost : simpl never.
Arguments tc16_cost : simpl never.
Arguments tc17_cost : simpl never.
Arguments tc18_cost : simpl never.
Arguments tc19_cost : simpl never.
Arguments tc20_cost : simpl never.
Arguments tc21_cost : simpl never.
Arguments tc22_cost : simpl never.
Arguments tc23_cost : simpl never.
Arguments tc24_cost : simpl never.
Arguments tc25_cost : simpl never.
Lemma upd_time t tC c cC a aC : (cost (extract (extract (upd_cost stepsCM t tC) c cC) a aC) <= 200)%nat.
Proof.
  unfold upd_cost. cost_simpl.
  pose proof (tc0_time t tC) as P0; cost_align P0.
  pose proof (tc1_time t tC) as P1; cost_align P1.
  pose proof (tc2_time t tC) as P2; cost_align P2.
  pose proof (tc3_time t tC) as P3; cost_align P3.
  pose proof (tc4_time t tC) as P4; cost_align P4.
  pose proof (tc5_time t tC) as P5; cost_align P5.
  pose proof (tc6_time t tC) as P6; cost_align P6.
  pose proof (tc7_time t tC) as P7; cost_align P7.
  pose proof (tc8_time t tC) as P8; cost_align P8.
  pose proof (tc9_time t tC) as P9; cost_align P9.
  pose proof (tc10_time t tC) as P10; cost_align P10.
  pose proof (tc11_time t tC) as P11; cost_align P11.
  pose proof (tc12_time t tC) as P12; cost_align P12.
  pose proof (tc13_time t tC) as P13; cost_align P13.
  pose proof (tc14_time t tC) as P14; cost_align P14.
  pose proof (tc15_time t tC) as P15; cost_align P15.
  pose proof (tc16_time t tC) as P16; cost_align P16.
  pose proof (tc17_time t tC) as P17; cost_align P17.
  pose proof (tc18_time t tC) as P18; cost_align P18.
  pose proof (tc19_time t tC) as P19; cost_align P19.
  pose proof (tc20_time t tC) as P20; cost_align P20.
  pose proof (tc21_time t tC) as P21; cost_align P21.
  pose proof (tc22_time t tC) as P22; cost_align P22.
  pose proof (tc23_time t tC) as P23; cost_align P23.
  pose proof (tc24_time t tC) as P24; cost_align P24.
  pose proof (tc25_time t tC) as P25; cost_align P25.
  repeat (match goal with |- context [(c <? ?k)%uint63] => destruct (c <? k) end; cbn).
  all: lia.
Qed.

Lemma sel_time t tC c cC : (cost (extract (sel_cost stepsCM t tC) c cC) <= 30)%nat.
Proof.
  unfold sel_cost. cost_simpl.
  pose proof (tc0_time t tC) as P0; cost_align P0.
  pose proof (tc1_time t tC) as P1; cost_align P1.
  pose proof (tc2_time t tC) as P2; cost_align P2.
  pose proof (tc3_time t tC) as P3; cost_align P3.
  pose proof (tc4_time t tC) as P4; cost_align P4.
  pose proof (tc5_time t tC) as P5; cost_align P5.
  pose proof (tc6_time t tC) as P6; cost_align P6.
  pose proof (tc7_time t tC) as P7; cost_align P7.
  pose proof (tc8_time t tC) as P8; cost_align P8.
  pose proof (tc9_time t tC) as P9; cost_align P9.
  pose proof (tc10_time t tC) as P10; cost_align P10.
  pose proof (tc11_time t tC) as P11; cost_align P11.
  pose proof (tc12_time t tC) as P12; cost_align P12.
  pose proof (tc13_time t tC) as P13; cost_align P13.
  pose proof (tc14_time t tC) as P14; cost_align P14.
  pose proof (tc15_time t tC) as P15; cost_align P15.
  pose proof (tc16_time t tC) as P16; cost_align P16.
  pose proof (tc17_time t tC) as P17; cost_align P17.
  pose proof (tc18_time t tC) as P18; cost_align P18.
  pose proof (tc19_time t tC) as P19; cost_align P19.
  pose proof (tc20_time t tC) as P20; cost_align P20.
  pose proof (tc21_time t tC) as P21; cost_align P21.
  pose proof (tc22_time t tC) as P22; cost_align P22.
  pose proof (tc23_time t tC) as P23; cost_align P23.
  pose proof (tc24_time t tC) as P24; cost_align P24.
  pose proof (tc25_time t tC) as P25; cost_align P25.
  repeat (match goal with |- context [(c <? ?k)%uint63] => destruct (c <? k) end; cbn).
  all: lia.
Qed.
Arguments sel_cost : simpl never.
Arguments upd_cost : simpl never.

Ltac gen_bound T X L :=
  let Hc := fresh "Hc" in
  pose proof (L : (@cost T X <= _)%nat) as Hc;
  revert Hc; generalize (@cost T X); intros ? Hc.

Ltac gen_costs := repeat match goal with |- context [@cost ?T ?X] =>
  lazymatch X with
  | extract (sel_cost stepsCM ?t ?tC) ?c ?cC => gen_bound T X (sel_time t tC c cC)
  | sel_cost stepsCM ?t ?tC => change (@cost T X) with 0%nat
  | extract (extract (upd_cost stepsCM ?t ?tC) ?c ?cC) ?a ?aC => gen_bound T X (upd_time t tC c cC a aC)
  | extract (upd_cost stepsCM ?t ?tC) ?c ?cC => change (@cost T X) with 0%nat
  | upd_cost stepsCM ?t ?tC => change (@cost T X) with 0%nat
  | set_cost _ _ _ => change (@cost T X) with 0%nat
  | extract (set_cost _ _ _) _ _ => change (@cost T X) with 0%nat
  | extract (extract (set_cost _ _ _) _ _) _ _ => change (@cost T X) with 0%nat
  | extract (extract (extract (set_cost _ _ _) _ _) _ _) _ _ => change (@cost T X) with 1%nat
  | make_cost _ _ _ => change (@cost T X) with 0%nat
  | extract (make_cost _ _ _) _ _ => change (@cost T X) with 0%nat
  | extract (extract (make_cost _ _ _) _ _) _ _ => change (@cost T X) with 1%nat
  end end.

Lemma tget_time t tC c cC n nC : (cost (extract (extract (tget_cost stepsCM t tC) c cC) n nC) <= 40)%nat.
Proof. unfold tget_cost. cost_simpl. gen_costs. lia. Qed.
Lemma tset_time t tC c cC n nC v vC : (cost (extract (extract (extract (tset_cost stepsCM t tC) c cC) n nC) v vC) <= 300)%nat.
Proof. unfold tset_cost. cost_simpl. gen_costs. lia. Qed.
Lemma mk_tab_time cap capC : (cost (mk_tab_cost stepsCM cap capC) <= 200)%nat.
Proof. unfold mk_tab_cost. cost_simpl. gen_costs. lia. Qed.
Lemma bdec_time b (w : bool_cost stepsCM b) : (cost (bdec_cost stepsCM b w) <= 2)%nat.
Proof. destruct w; cbn; lia. Qed.

Arguments tget_cost : simpl never.
Arguments tset_cost : simpl never.
Arguments mk_tab_cost : simpl never.
Arguments bdec_cost : simpl never.

Ltac gen_all := repeat match goal with |- context [@cost ?T ?X] =>
  lazymatch X with
  | extract (sel_cost stepsCM ?t ?tC) ?c ?cC => gen_bound T X (sel_time t tC c cC)
  | sel_cost stepsCM ?t ?tC => change (@cost T X) with 0%nat
  | extract (extract (upd_cost stepsCM ?t ?tC) ?c ?cC) ?a ?aC => gen_bound T X (upd_time t tC c cC a aC)
  | extract (upd_cost stepsCM ?t ?tC) ?c ?cC => change (@cost T X) with 0%nat
  | upd_cost stepsCM ?t ?tC => change (@cost T X) with 0%nat
  | extract (extract (tget_cost stepsCM ?t ?tC) ?c ?cC) ?n ?nC => gen_bound T X (tget_time t tC c cC n nC)
  | extract (tget_cost stepsCM ?t ?tC) ?c ?cC => change (@cost T X) with 0%nat
  | tget_cost stepsCM ?t ?tC => change (@cost T X) with 0%nat
  | extract (extract (extract (tset_cost stepsCM ?t ?tC) ?c ?cC) ?n ?nC) ?v ?vC => gen_bound T X (tset_time t tC c cC n nC v vC)
  | extract (extract (tset_cost stepsCM ?t ?tC) ?c ?cC) ?n ?nC => change (@cost T X) with 0%nat
  | extract (tset_cost stepsCM ?t ?tC) ?c ?cC => change (@cost T X) with 0%nat
  | tset_cost stepsCM ?t ?tC => change (@cost T X) with 0%nat
  | mk_tab_cost stepsCM ?c ?cC => gen_bound T X (mk_tab_time c cC)
  | bdec_cost stepsCM ?b ?w => gen_bound T X (bdec_time b w)
  | set_cost _ _ _ => change (@cost T X) with 0%nat
  | extract (set_cost _ _ _) _ _ => change (@cost T X) with 0%nat
  | extract (extract (set_cost _ _ _) _ _) _ _ => change (@cost T X) with 0%nat
  | extract (extract (extract (set_cost _ _ _) _ _) _ _) _ _ => change (@cost T X) with 1%nat
  | make_cost _ _ _ => change (@cost T X) with 0%nat
  | extract (make_cost _ _ _) _ _ => change (@cost T X) with 0%nat
  | extract (extract (make_cost _ _ _) _ _) _ _ => change (@cost T X) with 1%nat
  end end.

Lemma gap_step n i : (i <? n) = true -> forall m, (Z.to_nat (gap n i) <= S m)%nat ->
  (Z.to_nat (gap n (i + 1)) <= m)%nat.
Proof.
  intros Hi m Hm. pose proof (proj1 (Uint63.ltb_spec _ _) Hi).
  assert (φ (i + 1) = φ i + 1)%Z by (zify; Z.to_euclidean_division_equations; lia).
  unfold gap in *. lia.
Qed.

Lemma ins_loop_time w wC L LC T TC cnt cntC sz szC i iC n nC s sC H HC :
  (cost (extract (extract (extract (extract (extract (extract (extract (extract (ins_loop_cost stepsCM w wC) L LC) T TC) cnt cntC) sz szC) i iC) n nC) s sC) H HC)
     <= Z.to_nat (gap L i) * 500 + 20)%nat.
Proof.
  unfold ins_loop_cost. cbn.
  match goal with |- context [@cost ?Ty (?G w wC L LC T TC cnt cntC sz szC i iC n nC s sC H HC)] =>
    assert (HG : forall m T TC cnt cntC sz szC i iC n nC s sC H HC, (Z.to_nat (gap L i) <= m)%nat ->
       (cost (G w wC L LC T TC cnt cntC sz szC i iC n nC s sC H HC) <= m * 500 + 20)%nat) end.
  { induction m as [|m IH]; intros T' TC' cnt' cntC' sz' szC' i' iC' n' nC' s' sC' [g] HC' Hm.
    { cost_simpl.
      pose proof (bdec_time (i' <? L) (bool_w (i' <? L))) as HB.
      cost_destruct (bdec (i' <? L)).
      - exfalso. pose proof (proj1 (Uint63.ltb_spec _ _) e). unfold gap in Hm. lia.
      - cost_simpl. lia. }
    cost_simpl.
    pose proof (bdec_time (i' <? L) (bool_w (i' <? L))) as HB.
    cost_destruct (bdec (i' <? L)).
    - cost_simpl.
      pose proof (gap_step L i' e m Hm) as Hm'.
      cost_destruct ((sel T' (PrimString.get w i' - 97)).[n'] =? 0); cost_simpl.
      + gen_all.
        match goal with |- context [@cost ?Ty (?F w wC L LC ?a1 ?a2 ?a3 ?a4 ?a5 ?a6 ?a7 ?a8 ?a9 ?a10 ?a11 ?a12 ?h ?e)] =>
          gen_bound Ty (F w wC L LC a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 h e) (IH a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 h e Hm') end.
        lia.
      + gen_all.
        match goal with |- context [@cost ?Ty (?F w wC L LC ?a1 ?a2 ?a3 ?a4 ?a5 ?a6 ?a7 ?a8 ?a9 ?a10 ?a11 ?a12 ?h ?e)] =>
          gen_bound Ty (F w wC L LC a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 h e) (IH a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 h e Hm') end.
        lia.
    - cost_simpl. gen_all. lia. }
  match goal with |- context [@cost ?Ty (?G w wC L LC T TC cnt cntC sz szC i iC n nC s sC H HC)] =>
    exact (HG _ T TC cnt cntC sz szC i iC n nC s sC H HC (le_n _) : (@cost Ty (G w wC L LC T TC cnt cntC sz szC i iC n nC s sC H HC) <= _)%nat) end.
Qed.

Lemma qwalk_time q qC L LC T TC cnt cntC endv endvC N NC i iC n nC s sC H HC :
  (cost (extract (extract (extract (extract (extract (extract (extract (extract (extract (qwalk_cost stepsCM q qC) L LC) T TC) cnt cntC) endv endvC) N NC) i iC) n nC) s sC) H HC)
     <= Z.to_nat (gap L i) * 500 + 30)%nat.
Proof.
  unfold qwalk_cost. cbn.
  match goal with |- context [@cost ?Ty (?G q qC L LC T TC cnt cntC endv endvC N NC i iC n nC s sC H HC)] =>
    assert (HG : forall m i iC n nC s sC H HC, (Z.to_nat (gap L i) <= m)%nat ->
       (cost (G q qC L LC T TC cnt cntC endv endvC N NC i iC n nC s sC H HC) <= m * 500 + 30)%nat) end.
  { induction m as [|m IH]; intros i' iC' n' nC' s' sC' [g] HC' Hm.
    { cost_simpl.
      pose proof (bdec_time (i' <? L) (bool_w (i' <? L))) as HB.
      cost_destruct (bdec (i' <? L)).
      - exfalso. pose proof (proj1 (Uint63.ltb_spec _ _) e). unfold gap in Hm. lia.
      - cost_simpl. gen_all. cost_destruct (endv.[n'] =? 0); cost_simpl; gen_all; lia. }
    cost_simpl.
    pose proof (bdec_time (i' <? L) (bool_w (i' <? L))) as HB.
      cost_destruct (bdec (i' <? L)).
    - cost_simpl.
      pose proof (gap_step L i' e m Hm) as Hm'.
      cost_destruct ((sel T (PrimString.get q i' - 97)).[n'] =? 0); cost_simpl.
      + gen_all. lia.
      + gen_all.
        match goal with |- context [@cost ?Ty (?F q qC L LC T TC cnt cntC endv endvC N NC ?a1 ?a2 ?a3 ?a4 ?a5 ?a6 ?h ?e)] =>
          gen_bound Ty (F q qC L LC T TC cnt cntC endv endvC N NC a1 a2 a3 a4 a5 a6 h e) (IH a1 a2 a3 a4 a5 a6 h e Hm') end.
        lia.
    - cost_simpl. gen_all. cost_destruct (endv.[n'] =? 0); cost_simpl; gen_all; lia. }
  match goal with |- context [@cost ?Ty (?G q qC L LC T TC cnt cntC endv endvC N NC i iC n nC s sC H HC)] =>
    exact (HG _ i iC n nC s sC H HC (le_n _) : (@cost Ty (G q qC L LC T TC cnt cntC endv endvC N NC i iC n nC s sC H HC) <= _)%nat) end.
Qed.

Lemma total_time db dbC N NC j jC acc accC H HC :
  (cost (extract (extract (extract (extract (total_cost stepsCM db dbC) N NC) j jC) acc accC) H HC)
     <= Z.to_nat (gap N j) * 50 + 20)%nat.
Proof.
  unfold total_cost. cbn.
  match goal with |- context [@cost ?Ty (?G db dbC N NC j jC acc accC H HC)] =>
    assert (HG : forall m j jC acc accC H HC, (Z.to_nat (gap N j) <= m)%nat ->
       (cost (G db dbC N NC j jC acc accC H HC) <= m * 50 + 20)%nat) end.
  { induction m as [|m IH]; intros j' jC' acc' accC' [g] HC' Hm.
    { cost_simpl.
      pose proof (bdec_time (j' <? N) (bool_w (j' <? N))) as HB.
      cost_destruct (bdec (j' <? N)).
      - exfalso. pose proof (proj1 (Uint63.ltb_spec _ _) e). unfold gap in Hm. lia.
      - cost_simpl. gen_all. lia. }
    cost_simpl.
    pose proof (bdec_time (j' <? N) (bool_w (j' <? N))) as HB.
      cost_destruct (bdec (j' <? N)).
    - cost_simpl.
      pose proof (gap_step N j' e m Hm) as Hm'.
      gen_all.
      match goal with |- context [@cost ?Ty (?F db dbC N NC ?a1 ?a2 ?a3 ?a4 ?h ?e)] =>
        gen_bound Ty (F db dbC N NC a1 a2 a3 a4 h e) (IH a1 a2 a3 a4 h e Hm') end.
      lia.
    - cost_simpl. gen_all. lia. }
  match goal with |- context [@cost ?Ty (?G db dbC N NC j jC acc accC H HC)] =>
    exact (HG _ j jC acc accC H HC (le_n _) : (@cost Ty (G db dbC N NC j jC acc accC H HC) <= _)%nat) end.
Qed.

Lemma r_T_time r rC : (cost (r_T_cost stepsCM r rC) <= 2)%nat.
Proof. destruct rC. unfold r_T_cost. cbn. lia. Qed.
Lemma r_cnt_time r rC : (cost (r_cnt_cost stepsCM r rC) <= 2)%nat.
Proof. destruct rC. unfold r_cnt_cost. cbn. lia. Qed.
Lemma r_sz_time r rC : (cost (r_sz_cost stepsCM r rC) <= 2)%nat.
Proof. destruct rC. unfold r_sz_cost. cbn. lia. Qed.
Lemma r_n_time r rC : (cost (r_n_cost stepsCM r rC) <= 2)%nat.
Proof. destruct rC. unfold r_n_cost. cbn. lia. Qed.
Lemma r_s_time r rC : (cost (r_s_cost stepsCM r rC) <= 2)%nat.
Proof. destruct rC. unfold r_s_cost. cbn. lia. Qed.
Lemma b_T_time r rC : (cost (b_T_cost stepsCM r rC) <= 2)%nat.
Proof. destruct rC. unfold b_T_cost. cbn. lia. Qed.
Lemma b_cnt_time r rC : (cost (b_cnt_cost stepsCM r rC) <= 2)%nat.
Proof. destruct rC. unfold b_cnt_cost. cbn. lia. Qed.
Lemma b_end_time r rC : (cost (b_end_cost stepsCM r rC) <= 2)%nat.
Proof. destruct rC. unfold b_end_cost. cbn. lia. Qed.
Arguments r_T_cost : simpl never.
Arguments r_cnt_cost : simpl never.
Arguments r_sz_cost : simpl never.
Arguments r_n_cost : simpl never.
Arguments r_s_cost : simpl never.
Arguments b_T_cost : simpl never.
Arguments b_cnt_cost : simpl never.
Arguments b_end_cost : simpl never.
Arguments ins_loop_cost : simpl never.
Arguments qwalk_cost : simpl never.
Arguments total_cost : simpl never.

Ltac zero_costs F := repeat match goal with |- context [@cost ?T ?X] =>
  lazymatch X with context [F] => change (@cost T X) with 0%nat end end.

Lemma gap0 x : Z.to_nat (gap x 0) = Z.to_nat (φ x).
Proof. unfold gap. change (φ 0) with 0%Z. f_equal. lia. Qed.

Lemma query_time q qC T TC cnt cntC endv endvC N NC :
  (cost (extract (extract (extract (extract (query_cost stepsCM q qC) T TC) cnt cntC) endv endvC) N NC)
     <= size q * 500 + 60)%nat.
Proof.
  unfold query_cost. cost_simpl. zero_costs qwalk_cost.
  match goal with |- context [@cost ?Ty (extract (extract (extract (extract (extract (extract (extract (extract (extract (qwalk_cost stepsCM ?q1 ?q1C) ?L ?LC) ?T1 ?T1C) ?c1 ?c1C) ?e1 ?e1C) ?N1 ?N1C) ?i ?iC) ?n ?nC) ?s ?sC) ?h ?hc)] =>
    gen_bound Ty (extract (extract (extract (extract (extract (extract (extract (extract (extract (qwalk_cost stepsCM q1 q1C) L LC) T1 T1C) c1 c1C) e1 e1C) N1 N1C) i iC) n nC) s sC) h hc)
      (qwalk_time q1 q1C L LC T1 T1C c1 c1C e1 e1C N1 N1C i iC n nC s sC h hc) end.
  rewrite gap0 in Hc. change (size q) with (Z.to_nat (φ (PrimString.length q))). lia.
Qed.
Arguments query_cost : simpl never.

Fixpoint ssum (f : nat -> nat) (s k : nat) : nat :=
  match k with O => O | S k' => (f s + ssum f (S s) k')%nat end.

Definition wl (t : array PrimString.string) (j : nat) : nat :=
  size t.[Uint63.of_Z (Z.of_nat j)].

Lemma wl_at t k : wl t (Z.to_nat (φ k)) = size t.[k].
Proof.
  unfold wl. rewrite Z2Nat.id; [apply to_Z_bounded|]. rewrite of_to_Z. reflexivity.
Qed.

Lemma ssum_step f Q k m : (k <? Q) = true ->
  ssum f (Z.to_nat (φ k)) (S m) = (f (Z.to_nat (φ k)) + ssum f (Z.to_nat (φ (k + 1))) m)%nat.
Proof.
  intros Hk. pose proof (proj1 (Uint63.ltb_spec _ _) Hk).
  assert (E : φ (k + 1) = (φ k + 1)%Z) by (zify; Z.to_euclidean_division_equations; lia).
  assert (E2 : Z.to_nat (φ (k + 1)) = S (Z.to_nat (φ k))) by (rewrite E; pose proof (to_Z_bounded k); lia).
  rewrite E2. reflexivity.
Qed.

Lemma gap_step_eq n i m : (i <? n) = true -> Z.to_nat (gap n i) = S m ->
  Z.to_nat (gap n (i + 1)) = m.
Proof.
  intros Hi Hm. pose proof (proj1 (Uint63.ltb_spec _ _) Hi).
  assert (φ (i + 1) = φ i + 1)%Z by (zify; Z.to_euclidean_division_equations; lia).
  unfold gap in *. lia.
Qed.

Arguments ssum : simpl never.
Arguments wl : simpl never.

Lemma answer_time qs qsC Q QC T TC cnt cntC endv endvC N NC out outC k kC H HC :
  (cost (extract (extract (extract (extract (extract (extract (extract (extract (answer_cost stepsCM qs qsC) Q QC) T TC) cnt cntC) endv endvC) N NC) out outC) k kC) H HC)
     <= ssum (wl qs) (Z.to_nat (φ k)) (Z.to_nat (gap Q k)) * 500 + Z.to_nat (gap Q k) * 200 + 20)%nat.
Proof.
  unfold answer_cost. cbn.
  match goal with |- context [@cost ?Ty (?G qs qsC Q QC T TC cnt cntC endv endvC N NC out outC k kC H HC)] =>
    assert (HG : forall m out outC k kC H HC, Z.to_nat (gap Q k) = m ->
       (cost (G qs qsC Q QC T TC cnt cntC endv endvC N NC out outC k kC H HC)
         <= ssum (wl qs) (Z.to_nat (φ k)) m * 500 + m * 200 + 20)%nat) end.
  { induction m as [|m IH]; intros out' outC' k' kC' [g] HC' Hm.
    { cost_simpl.
      pose proof (bdec_time (k' <? Q) (bool_w (k' <? Q))) as HB.
      cost_destruct (bdec (k' <? Q)).
      - exfalso. pose proof (proj1 (Uint63.ltb_spec _ _) e). unfold gap in Hm. lia.
      - cost_simpl. gen_all. lia. }
    cost_simpl.
    pose proof (bdec_time (k' <? Q) (bool_w (k' <? Q))) as HB.
    cost_destruct (bdec (k' <? Q)).
    - cost_simpl.
      pose proof (gap_step_eq Q k' m e Hm) as Hm'.
      rewrite (ssum_step _ Q k' m e) wl_at.
      gen_all. zero_costs query_cost.
      match goal with |- context [@cost ?Ty (extract (extract (extract (extract (query_cost stepsCM ?q1 ?q1C) ?T1 ?T1C) ?c1 ?c1C) ?e1 ?e1C) ?N1 ?N1C)] =>
        gen_bound Ty (extract (extract (extract (extract (query_cost stepsCM q1 q1C) T1 T1C) c1 c1C) e1 e1C) N1 N1C)
          (query_time q1 q1C T1 T1C c1 c1C e1 e1C N1 N1C) end.
      match goal with |- context [@cost ?Ty (?F qs qsC Q QC T TC cnt cntC endv endvC N NC ?a1 ?a2 ?a3 ?a4 ?h ?e)] =>
        gen_bound Ty (F qs qsC Q QC T TC cnt cntC endv endvC N NC a1 a2 a3 a4 h e) (IH a1 a2 a3 a4 h e Hm') end.
      lia.
    - cost_simpl. gen_all. lia. }
  match goal with |- context [@cost ?Ty (?G qs qsC Q QC T TC cnt cntC endv endvC N NC out outC k kC H HC)] =>
    exact (HG _ out outC k kC H HC eq_refl : (@cost Ty (G qs qsC Q QC T TC cnt cntC endv endvC N NC out outC k kC H HC) <= _)%nat) end.
Qed.

Ltac gen_proj := repeat match goal with |- context [@cost ?T ?X] =>
  lazymatch X with
  | r_T_cost stepsCM ?r ?rC => gen_bound T X (r_T_time r rC)
  | r_cnt_cost stepsCM ?r ?rC => gen_bound T X (r_cnt_time r rC)
  | r_sz_cost stepsCM ?r ?rC => gen_bound T X (r_sz_time r rC)
  | r_n_cost stepsCM ?r ?rC => gen_bound T X (r_n_time r rC)
  | r_s_cost stepsCM ?r ?rC => gen_bound T X (r_s_time r rC)
  | b_T_cost stepsCM ?r ?rC => gen_bound T X (b_T_time r rC)
  | b_cnt_cost stepsCM ?r ?rC => gen_bound T X (b_cnt_time r rC)
  | b_end_cost stepsCM ?r ?rC => gen_bound T X (b_end_time r rC)
  end end.

Lemma build_time db dbC N NC T TC cnt cntC endv endvC sz szC j jC H HC :
  (cost (extract (extract (extract (extract (extract (extract (extract (build_cost stepsCM db dbC) N NC) T TC) cnt cntC) endv endvC) sz szC) j jC) H HC)
     <= ssum (wl db) (Z.to_nat (φ j)) (Z.to_nat (gap N j)) * 500 + Z.to_nat (gap N j) * 300 + 20)%nat.
Proof.
  unfold build_cost. cbn.
  match goal with |- context [@cost ?Ty (?G db dbC N NC T TC cnt cntC endv endvC sz szC j jC H HC)] =>
    assert (HG : forall m T TC cnt cntC endv endvC sz szC j jC H HC, Z.to_nat (gap N j) = m ->
       (cost (G db dbC N NC T TC cnt cntC endv endvC sz szC j jC H HC)
         <= ssum (wl db) (Z.to_nat (φ j)) m * 500 + m * 300 + 20)%nat) end.
  { induction m as [|m IH]; intros T' TC' cnt' cntC' endv' endvC' sz' szC' j' jC' [g] HC' Hm.
    { remember (ssum (wl db) (Z.to_nat (φ j')) 0 * 500 + 0 * 300 + 20)%nat as R eqn:HR.
      cost_simpl.
      pose proof (bdec_time (j' <? N) (bool_w (j' <? N))) as HB.
      cost_destruct (bdec (j' <? N)).
      - exfalso. pose proof (proj1 (Uint63.ltb_spec _ _) e). unfold gap in Hm. lia.
      - cost_simpl. gen_all. subst R. lia. }
    remember (ssum (wl db) (Z.to_nat (φ j')) (S m) * 500 + S m * 300 + 20)%nat as R eqn:HR.
    cost_simpl.
    pose proof (bdec_time (j' <? N) (bool_w (j' <? N))) as HB.
    cost_destruct (bdec (j' <? N)).
    - cost_simpl.
      pose proof (gap_step_eq N j' m e Hm) as Hm'.
      gen_all. gen_proj.
      match goal with |- context [@cost ?Ty (extract (extract (extract (extract (extract (extract (extract (extract (ins_loop_cost stepsCM ?w ?wC) ?L ?LC) ?T1 ?T1C) ?c1 ?c1C) ?s1 ?s1C) ?i ?iC) ?n ?nC) ?s ?sC) ?h ?hc)] =>
        gen_bound Ty (extract (extract (extract (extract (extract (extract (extract (extract (ins_loop_cost stepsCM w wC) L LC) T1 T1C) c1 c1C) s1 s1C) i iC) n nC) s sC) h hc)
          (ins_loop_time w wC L LC T1 T1C c1 c1C s1 s1C i iC n nC s sC h hc) end.
      zero_costs ins_loop_cost.
      match goal with |- context [@cost ?Ty (?F db dbC N NC ?a1 ?a2 ?a3 ?a4 ?a5 ?a6 ?a7 ?a8 ?a9 ?a10 ?h ?e)] =>
        gen_bound Ty (F db dbC N NC a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 h e) (IH a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 h e Hm') end.
      subst R. rewrite (ssum_step _ N j' m e) wl_at.
      repeat match goal with Hc : context [gap (PrimString.length ?w) 0] |- _ => rewrite gap0 in Hc end.
      change (size db.[j']) with (Z.to_nat (φ (PrimString.length db.[j']))).
      lia.
    - cost_simpl. gen_all. subst R. lia. }
  match goal with |- context [@cost ?Ty (?G db dbC N NC T TC cnt cntC endv endvC sz szC j jC H HC)] =>
    exact (HG _ T TC cnt cntC endv endvC sz szC j jC H HC eq_refl : (@cost Ty (G db dbC N NC T TC cnt cntC endv endvC sz szC j jC H HC) <= _)%nat) end.
Qed.

Arguments answer_cost : simpl never.
Arguments build_cost : simpl never.

Lemma baza_impl_time db dbC qs qsC :
  (cost (extract (baza_impl_cost stepsCM db dbC) qs qsC)
    <= ssum (wl db) 0 (size db) * 500 + ssum (wl qs) 0 (size qs) * 500 + size db * 400 + size qs * 200 + 1000)%nat.
Proof.
  remember (ssum (wl db) 0 (size db) * 500 + ssum (wl qs) 0 (size qs) * 500 + size db * 400 + size qs * 200 + 1000)%nat as R eqn:HR.
  unfold baza_impl_cost. cost_simpl.
  match goal with |- context [@cost ?Ty (extract (extract (extract (extract (total_cost stepsCM ?a ?aC) ?b ?bC) ?c ?cC) ?d ?dC) ?h ?hc)] =>
    gen_bound Ty (extract (extract (extract (extract (total_cost stepsCM a aC) b bC) c cC) d dC) h hc)
      (total_time a aC b bC c cC d dC h hc) end.
  match goal with |- context [@cost ?Ty (extract (extract (extract (extract (extract (extract (extract (build_cost stepsCM ?a ?aC) ?b ?bC) ?c ?cC) ?d ?dC) ?e ?eC) ?f ?fC) ?g ?gC) ?h ?hc)] =>
    gen_bound Ty (extract (extract (extract (extract (extract (extract (extract (build_cost stepsCM a aC) b bC) c cC) d dC) e eC) f fC) g gC) h hc)
      (build_time a aC b bC c cC d dC e eC f fC g gC h hc) end.
  match goal with |- context [@cost ?Ty (extract (extract (extract (extract (extract (extract (extract (extract (answer_cost stepsCM ?a ?aC) ?b ?bC) ?c ?cC) ?d ?dC) ?e ?eC) ?f ?fC) ?g ?gC) ?i ?iC) ?h ?hc)] =>
    gen_bound Ty (extract (extract (extract (extract (extract (extract (extract (extract (answer_cost stepsCM a aC) b bC) c cC) d dC) e eC) f fC) g gC) i iC) h hc)
      (answer_time a aC b bC c cC d dC e eC f fC g gC i iC h hc) end.
  zero_costs total_cost. zero_costs build_cost. zero_costs answer_cost.
  gen_all. gen_proj.
  repeat match goal with Hc : context [gap ?x 0] |- _ => rewrite gap0 in Hc end.
  change (φ 0) with 0%Z in *. 
  change (Z.to_nat (φ (length db))) with (size db) in *.
  change (Z.to_nat (φ (length qs))) with (size qs) in *.
  change (Z.to_nat 0) with 0%nat in *.
  subst R. lia.
Qed.

Lemma fold_ssum (f : nat -> nat) s k a :
  fold_left (fun acc i => (acc + f i)%nat) (seq s k) a = (a + ssum f s k)%nat.
Proof.
  revert s a. induction k as [|k IHk]; intros s a.
  - cbn. change (ssum f s 0) with 0%nat. lia.
  - cbn [seq fold_left]. rewrite IHk.
    change (ssum f s (S k)) with (f s + ssum f (S s) k)%nat. lia.
Qed.

Lemma sizes_ssum (t : array PrimString.string) : sizes t = ssum (wl t) 0 (size t).
Proof. exact (fold_ssum (wl t) 0 (size t) 0). Qed.

Arguments baza_impl_cost : simpl never.

Theorem baza_time : exists c1 c2 : nat,
  forall (database queries : list String.string)
  (database_arr queries_arr : array
  PrimString.string),
  valid_input database queries ->
  repr database_arr database -> repr queries_arr queries ->
  (cost2 baza_cost database_arr queries_arr <= c1 * (sizes database_arr + sizes queries_arr + size database_arr + size queries_arr + 1) + c2)%nat.
Proof.
  exists 500%nat, 1000%nat.
  intros db qs x y _ _ _.
  rewrite !sizes_ssum.
  remember (500 * (ssum (wl x) 0 (size x) + ssum (wl y) 0 (size y) + size x + size y + 1) + 1000)%nat as R eqn:HR.
  unfold cost2. rewrite call_cost2_eq. unfold baza_cost. cost_simpl.
  zero_costs baza_impl_cost.
  pose proof (baza_impl_time x (witness x) y (witness y)) as Hb. cost_align Hb.
  subst R. lia.
Qed.
