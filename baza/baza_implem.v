(* Executable implementation and its required termination dependencies.
   Correctness proofs are in baza_proofs.v. *)
(* Implementation of baza (baza.spec): a trie of the database words with
   a counter per node, built once in database order; every query answered
   offline against it.  See README.md, "Implementation". *)

From Speck Require Import Prelude.
From Respeced Require Import Repr.
From Stdlib Require Import ZArith NArith List Uint63 PArray ZifyUint63 Lia Zwf.
From Stdlib Require String Ascii PrimString.
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

Definition mk_tab (cap : int) : tab :=
  mkT (PArray.make cap 0) (PArray.make cap 0) (PArray.make cap 0) (PArray.make cap 0) (PArray.make cap 0) (PArray.make cap 0) (PArray.make cap 0) (PArray.make cap 0) (PArray.make cap 0) (PArray.make cap 0) (PArray.make cap 0) (PArray.make cap 0) (PArray.make cap 0) (PArray.make cap 0) (PArray.make cap 0) (PArray.make cap 0) (PArray.make cap 0) (PArray.make cap 0) (PArray.make cap 0) (PArray.make cap 0) (PArray.make cap 0) (PArray.make cap 0) (PArray.make cap 0) (PArray.make cap 0) (PArray.make cap 0) (PArray.make cap 0).

(* child of node n by letter c, and its update *)
Definition tget (t : tab) (c n : int) : int := (sel t c).[n].
Definition tset (t : tab) (c n v : int) : tab := upd t c ((sel t c).[n <- v]).

(* ------------------------------------------------------------------ *)
(* The program                                                         *)
(* ------------------------------------------------------------------ *)

Record ires : Type := mkI
  { r_T : tab; r_cnt : array int; r_sz : int; r_n : int; r_s : int }.

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

Record bres : Type := mkB { b_T : tab; b_cnt : array int; b_end : array int }.

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

Definition query (q : PrimString.string) (T : tab) (cnt endv : array int) (N : int) : int :=
  qwalk q (PrimString.length q) T cnt endv N 0 0 0
    (Zwf_well_founded 0 (gap (PrimString.length q) 0)).

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

(* acc + the total length of the words j .. N-1 *)
Fixpoint total (db : array PrimString.string) (N j acc : int)
    (H : Acc (Zwf 0) (gap N j)) {struct H} : int :=
  match bdec (j <? N) with
  | left Hj => total db N (j + 1) (acc + PrimString.length db.[j])
                 (Acc_inv H (dec_step N j Hj))
  | right _ => acc
  end.

Definition baza_impl (db qs : array PrimString.string) : array uint :=
  let N := PArray.length db in
  let cap := 1 + total db N 0 0 (Zwf_well_founded 0 (gap N 0)) in
  let b := build db N (mk_tab cap) (PArray.make cap 0) (PArray.make cap 0) 1 0
             (Zwf_well_founded 0 (gap N 0)) in
  let Q := PArray.length qs in
  answer qs Q (b_T b) (b_cnt b) (b_end b) N (PArray.make Q 0) 0
    (Zwf_well_founded 0 (gap Q 0)).

(* ------------------------------------------------------------------ *)
(* Math side: a word is the list of its letter indices (code - 97)     *)
(* ------------------------------------------------------------------ *)

Open Scope list_scope.

(* ------------------------------------------------------------------ *)
(* The spec's items, at top level                                      *)
(* ------------------------------------------------------------------ *)

Definition baza : array PrimString.string -> array PrimString.string -> array uint :=
  baza_impl.
