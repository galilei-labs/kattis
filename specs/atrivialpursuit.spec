(* @function        atrivialpursuit
   @signature       uint -> array uint -> array uint -> uint
   @math_signature  N -> list N -> list N -> N
   @summary         [atrivialpursuit P gs ls] counts the sequences of P
                    positive integers whose gcd is G, the product of the
                    gs, and whose lcm is L, the product of the ls, and
                    returns that count modulo 10^9 + 7 (0 when no sequence
                    exists).
*)

From Stdlib Require Import ZArith NArith List Uint63 PArray.
From Respeced Require Import Repr.
Import ListNotations.
Open Scope N_scope.

(* Math side.  G and L can have 400 * 18 digits: they exist only here, as
   [N]; every input and the answer fit in a [uint]. *)

(* The number of elements of l. *)
Definition len {A} (l : list A) : N := N.of_nat (List.length l).

(* The product of the elements of l (G_1 * ... * G_N, L_1 * ... * L_M). *)
Definition prod (l : list N) : N := fold_right N.mul 1 l.

Definition seq_gcd (xs : list N) : N := fold_right N.gcd 0 xs.
Definition seq_lcm (xs : list N) : N := fold_right N.lcm 1 xs.

(* xs = x_1, ..., x_P : P positive integers with gcd g and lcm l. *)
Definition is_sequence (P g l : N) (xs : list N) : Prop :=
  len xs = P /\ Forall (fun x => 0 < x) xs /\
  seq_gcd xs = g /\ seq_lcm xs = l.

(* Exactly c sequences satisfy is_sequence: s lists each of them once. *)
Definition num_sequences (P g l c : N) : Prop :=
  exists s : list (list N),
    NoDup s /\ (forall xs, In xs s <-> is_sequence P g l xs) /\
    len s = c.

(* The statement's bounds. *)
Record valid_input (P : N) (gs ls : list N) : Prop := {
  (* 1 <= P <= 10^18 *)
  vi_P : 1 <= P <= 10 ^ 18;
  (* 1 <= N, M <= 400 *)
  vi_N : 1 <= len gs <= 400;
  vi_M : 1 <= len ls <= 400;
  (* 1 <= G_i <= 10^18 *)
  vi_gs : Forall (fun g => 1 <= g <= 10 ^ 18) gs;
  (* 1 <= L_i <= 10^18 *)
  vi_ls : Forall (fun l => 1 <= l <= 10 ^ 18) ls;
}.

(* The answer: the number of such sequences, modulo 10^9 + 7. *)
Definition atrivialpursuit_spec (P : N) (gs ls : list N) (o : N) : Prop :=
  exists c, num_sequences P (prod gs) (prod ls) c /\
            o = c mod (10 ^ 9 + 7).

Program atrivialpursuit : uint -> array uint -> array uint -> uint.

Specification atrivialpursuit_correct :
  forall (P : N) (gs ls : list N) (p : uint) (x y : array uint),
  valid_input P gs ls -> repr p P -> repr x gs -> repr y ls ->
  exists o : N, repr (atrivialpursuit p x y) o /\
                atrivialpursuit_spec P gs ls o.

(* The kernel primitives (int, array, float, string) and their axioms. *)
Allowed Primitive Axioms.
