(* Executable implementation and its required termination dependencies.
   Correctness proofs are in plot_proofs.v. *)
(* Implementation of plot (plot.spec): the constants C_0, ..., C_n are the
   forward differences of p at 0, Delta^k p (0).

   Code.  [plot n y] (y = a_n, ..., a_0, length L = n+1) allocates one flat
   table d = [PArray.make L 0], fills d.[x] = p(x) for x = 0 .. L-1 by
   Horner's rule over y, then builds the difference table in place: stage
   s = 0 .. L-1 runs i from L-1 down to s+1 with d.[i] <- d.[i] - d.[i-1].
   After stage s, cell i holds Delta^(min i (s+1)) p (i - min i (s+1)), so at
   the end d.[k] = Delta^k p (0).  Everything is wrapping 63-bit [int]
   arithmetic; every value is exact modulo 2^63 and the final constants are
   bounded by 2^6 * 50 * 7 * 6^7 < 2^62, so the signed reading is exact.
   The degree argument n is not read: L is the length of y (= n+1).

   Termination: every loop recurses structurally on an erased
   [Acc (Zwf 0) (gap ...)] proof, as in template/polymul1.  The table is
   threaded linearly (each [set] on the latest version, its reads before
   it); y is only read.

   Proof.  Math side: [dk k f m] is Delta^k f (m); [polydeg d f] says
   Delta^(d+1) f = 0, closed under constants, sums, shifts and x * f; a
   polynomial with n+1 coefficients has [polydeg n].  The vector
   [Delta^0 f m; ...; Delta^n f m] is mapped by [step] to the same vector
   at m+1, so i iterations give f(i) at the head. *)

From Speck Require Import Prelude.
From Respeced Require Import Repr.
From Stdlib Require Import ZArith NArith List Uint63 PArray ZifyUint63 Lia Zwf.
From Stdlib Require Sint63.
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

Lemma dec_down : forall lo i : int,
  (lo <? i) = true -> Zwf 0 (gap (i - 1) lo) (gap i lo).
Proof.
  intros lo i H. rewrite ltb_spec in H.
  assert (H1 : (φ (i - 1)) = ((φ i) - 1)%Z) by sia.
  unfold Zwf, gap. lia.
Qed.

(* ------------------------------------------------------------------ *)
(* The program                                                         *)
(* ------------------------------------------------------------------ *)

(* Horner's rule: h * x^(len-j) + (y.[j] x^(len-j-1) + ... + y.[len-1]),
   modulo 2^63. *)
Fixpoint horner_loop (y : array int) (len x j h : int)
    (H : Acc (Zwf 0) (gap len j)) {struct H} : int :=
  match bdec (j <? len)%uint63 with
  | left Hj =>
      horner_loop y len x (j + 1) (h * x + y.[j])
        (Acc_inv H (dec_step len j Hj))
  | right _ => h
  end.

(* Cells x, x+1, ..., len-1 of d receive p(x). *)
Fixpoint eval_loop (y : array int) (len x : int) (d : array int)
    (H : Acc (Zwf 0) (gap len x)) {struct H} : array int :=
  match bdec (x <? len) with
  | left Hx =>
      eval_loop y len (x + 1)
        d.[x <- horner_loop y len x 0 0 (Zwf_well_founded 0 (gap len 0))]
        (Acc_inv H (dec_step len x Hx))
  | right _ => d
  end.

(* One stage of the difference table: i, i-1, ..., lo+1 receive
   d.[i] - d.[i-1]. *)
Fixpoint diff_inner (lo i : int) (d : array int)
    (H : Acc (Zwf 0) (gap i lo)) {struct H} : array int :=
  match bdec (lo <? i) with
  | left Hi =>
      let v := d.[i] - d.[i - 1] in
      diff_inner lo (i - 1) d.[i <- v] (Acc_inv H (dec_down lo i Hi))
  | right _ => d
  end.

(* Stages s, s+1, ..., len-1. *)
Fixpoint diff_outer (len s : int) (d : array int)
    (H : Acc (Zwf 0) (gap len s)) {struct H} : array int :=
  match bdec (s <? len)%uint63 with
  | left Hs =>
      diff_outer len (s + 1)
        (diff_inner s (len - 1) d (Zwf_well_founded 0 (gap (len - 1) s)))
        (Acc_inv H (dec_step len s Hs))
  | right _ => d
  end.

Definition plot_impl (n : uint) (y : array sint) : array sint :=
  let len := PArray.length y in
  let d := eval_loop y len 0 (PArray.make len 0%uint63)
             (Zwf_well_founded 0 (gap len 0)) in
  diff_outer len 0 d (Zwf_well_founded 0 (gap len 0)).

(* ------------------------------------------------------------------ *)
(* Math side: finite differences                                       *)
(* ------------------------------------------------------------------ *)

Open Scope Z_scope.

(* ------------------------------------------------------------------ *)
(* The spec's items, at top level                                      *)
(* ------------------------------------------------------------------ *)

Definition plot : uint -> array sint -> array sint := plot_impl.
