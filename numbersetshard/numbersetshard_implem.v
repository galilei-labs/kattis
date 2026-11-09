(* Executable implementation and its required termination dependencies.
   Correctness proofs are in numbersetshard_proofs.v. *)
(* Implementation of numbersetshard (numbersetshard.spec). *)

From Speck Require Import Prelude.
From Respeced Require Import Repr.
From Stdlib Require Import ZArith NArith List Uint63 PArray ZifyUint63 Lia Zwf
  Znumtheory Relations.
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

Definition rmeas (rk : array int) (x : int) : Z := (wB - (φ (rk.[x])))%Z.

Lemma rdec : forall (rk : array int) (x z : int),
  (rk.[x] <? rk.[z]) = true -> Zwf 0 (rmeas rk z) (rmeas rk x).
Proof.
  intros rk x z H. rewrite ltb_spec in H.
  pose proof (to_Z_bounded rk.[z]). unfold Zwf, rmeas. lia.
Qed.

(* ------------------------------------------------------------------ *)
(* The program                                                         *)
(* ------------------------------------------------------------------ *)

(* Sieve marking: cells j, j+i, ..., cnt - t of them, are set. *)
Fixpoint mark (c : array bool) (i cnt t j : int)
    (H : Acc (Zwf 0) (gap cnt t)) {struct H} : array bool :=
  match bdec (t <? cnt) with
  | left Ht => mark c.[j <- true] i cnt (t + 1) (j + i)
                 (Acc_inv H (dec_step cnt t Ht))
  | right _ => c
  end.

Definition mark_from (c : array bool) (w i : int) : array bool :=
  let s := i * i in
  let cnt := (w - s) / i + 1 in
  mark c i cnt 0 s (Zwf_well_founded 0 (gap cnt 0)).

(* Eratosthenes on c (length n = w + 1), from i on, while i * i <= w. *)
Fixpoint sieve (c : array bool) (w n i : int)
    (H : Acc (Zwf 0) (gap n i)) {struct H} : array bool :=
  match bdec (i <? n) with
  | left Hi =>
      if i * i <=? w then
        let c' := if c.[i] then c else mark_from c w i in
        sieve c' w n (i + 1) (Acc_inv H (dec_step n i Hi))
      else c
  | right _ => c
  end.

(* Find with path halving.  The rank test is always true on a valid
   forest; it is the termination argument. *)
Fixpoint find (par rk : array int) (x : int)
    (H : Acc (Zwf 0) (rmeas rk x)) {struct H} : int * array int :=
  let y := par.[x] in
  if y =? x then (x, par)
  else
    let z := par.[y] in
    match bdec (rk.[x] <? rk.[z]) with
    | left Hl => find par.[x <- z] rk z (Acc_inv H (rdec rk x z Hl))
    | right _ => (x, par)
    end.

(* Union by rank. *)
Definition union (par rk : array int) (u v : int) : array int * array int :=
  let (ru, par1) := find par rk u (Zwf_well_founded 0 (rmeas rk u)) in
  let (rv, par2) := find par1 rk v (Zwf_well_founded 0 (rmeas rk v)) in
  if ru =? rv then (par2, rk)
  else
    let ku := rk.[ru] in
    let kv := rk.[rv] in
    if ku <? kv then (par2.[ru <- rv], rk)
    else if kv <? ku then (par2.[rv <- ru], rk)
    else (par2.[ru <- rv], rk.[rv <- kv + 1]).

(* Union of the offsets o, o + q, o + 2q, ... (cnt - t links). *)
Fixpoint ulink (par rk : array int) (q cnt t o : int)
    (H : Acc (Zwf 0) (gap cnt t)) {struct H} : array int * array int :=
  match bdec (t <? cnt) with
  | left Ht =>
      let (par', rk') := union par rk o (o + q) in
      ulink par' rk' q cnt (t + 1) (o + q) (Acc_inv H (dec_step cnt t Ht))
  | right _ => (par, rk)
  end.

(* First offset o with q | a + o. *)
Definition first_off (a q : int) : int := (q - a mod q) mod q.

(* For every prime q in [q, n), link its multiples in [a, a + w]. *)
Fixpoint uprimes (c : array bool) (a w n : int) (par rk : array int) (q : int)
    (H : Acc (Zwf 0) (gap n q)) {struct H} : array int * array int :=
  match bdec (q <? n) with
  | left Hq =>
      let (par', rk') :=
        if c.[q] then (par, rk)
        else
          let o0 := first_off a q in
          ulink par rk q ((w - o0) / q) 0 o0
            (Zwf_well_founded 0 (gap ((w - o0) / q) 0)) in
      uprimes c a w n par' rk' (q + 1) (Acc_inv H (dec_step n q Hq))
  | right _ => (par, rk)
  end.

Fixpoint iota (par : array int) (n i : int)
    (H : Acc (Zwf 0) (gap n i)) {struct H} : array int :=
  match bdec (i <? n) with
  | left Hi => iota par.[i <- i] n (i + 1) (Acc_inv H (dec_step n i Hi))
  | right _ => par
  end.

Fixpoint count (par : array int) (n o acc : int)
    (H : Acc (Zwf 0) (gap n o)) {struct H} : int :=
  match bdec (o <? n) with
  | left Ho => count par n (o + 1) (if par.[o] =? o then acc + 1 else acc)
                 (Acc_inv H (dec_step n o Ho))
  | right _ => acc
  end.

Definition numbersets_impl (x y z : uint) : uint :=
  let w := y - x in
  let n := w + 1 in
  let c := sieve (PArray.make n false) w n 2 (Zwf_well_founded 0 (gap n 2)) in
  let par0 := iota (PArray.make n 0) n 0 (Zwf_well_founded 0 (gap n 0)) in
  let rk0 := PArray.make n 0 in
  let (par, rk) := uprimes c x w n par0 rk0 z (Zwf_well_founded 0 (gap n z)) in
  count par n 0 0 (Zwf_well_founded 0 (gap n 0)).

(* ------------------------------------------------------------------ *)
(* Sieve                                                               *)
(* ------------------------------------------------------------------ *)

Local Open Scope Z_scope.

(* ------------------------------------------------------------------ *)
(* Equivalence closures                                                *)
(* ------------------------------------------------------------------ *)

Notation crst := (clos_refl_sym_trans Z).

(* ------------------------------------------------------------------ *)
(* The spec's items, at top level                                      *)
(* ------------------------------------------------------------------ *)

Definition numbersets : uint -> uint -> uint -> uint := numbersets_impl.
