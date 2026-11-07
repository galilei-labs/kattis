(** * A Trivial Pursuit *)

(** ** Description *)

(** [atrivialpursuit term_count gcd_factors lcm_factors]
    counts the sequences of term_count (P) positive
    integers whose gcd is G, the product of the
    gcd_factors, and whose lcm is L, the product of the
    lcm_factors, and returns that count modulo 10^9 + 7
    (0 when no sequence exists).
    [@kattis atrivialpursuit]
    - Difficulty: 9.1 *)

(** ** [@hide] Environment *)

(* @function        atrivialpursuit
   @signature       uint -> array uint -> array uint -> uint
   @math_signature  N -> list N -> list N -> N
   @summary         [atrivialpursuit term_count gcd_factors lcm_factors]
                    counts the sequences of term_count (P) positive integers
                    whose gcd is G, the product of the gcd_factors, and
                    whose lcm is L, the product of the lcm_factors, and
                    returns that count modulo 10^9 + 7 (0 when no sequence
                    exists).
*)

From Stdlib Require Import ZArith NArith List Uint63 PArray.
From Respeced Require Import Repr.
Import ListNotations.
Open Scope N_scope.

(* Math side.  G and L can have 400 * 18 digits: they exist
  only here, as
   [N]; every input and the answer fit in a [uint]. *)

(** ** Definitions *)

(** The number of elements of l. *)
Definition len {A} (l : list A) : N :=
  N.of_nat (List.length l).

(** The product of the elements of l (G_1 * ... * G_N,
    L_1 * ... * L_M). *)
Definition prod (l : list N) : N := fold_right N.mul 1 l.

(** The greatest common divisor of the sequence. *)
Definition seq_gcd (terms : list N) : N :=
  fold_right N.gcd 0 terms.
(** The least common multiple of the sequence. *)
Definition seq_lcm (terms : list N) : N :=
  fold_right N.lcm 1 terms.

(** terms = x_1, ..., x_P : term_count (P) positive
    integers with gcd target_gcd and lcm target_lcm. *)
Definition is_sequence
  (term_count target_gcd target_lcm : N)
    (terms : list N) : Prop :=
  len terms = term_count /\ Forall
    (fun term => 0 < term) terms /\
  seq_gcd terms = target_gcd /\ seq_lcm terms = target_lcm.

(** Exactly sequence_count sequences satisfy
    is_sequence: sequences lists each of them once. *)
Definition num_sequences
  (term_count target_gcd target_lcm sequence_count
    : N) : Prop :=
  exists sequences : list (list N),
    NoDup sequences /\
    (forall terms, In terms sequences <->
       is_sequence term_count target_gcd target_lcm terms)
         /\
    len sequences = sequence_count.

(** [@inside atrivialpursuit_correct] The statement's
    bounds. *)
Record valid_input (term_count : N)
  (gcd_factors lcm_factors : list N)
    : Prop := {
  (* 1 <= P <= 10^18 *)
  vi_P : 1 <= term_count <= 10 ^ 18;
  (* 1 <= N, M <= 400 *)
  vi_N : 1 <= len gcd_factors <= 400;
  vi_M : 1 <= len lcm_factors <= 400;
  (* 1 <= G_i <= 10^18 *)
  vi_gs : Forall
    (fun factor => 1 <= factor <= 10 ^ 18) gcd_factors;
  (* 1 <= L_i <= 10^18 *)
  vi_ls : Forall
    (fun factor => 1 <= factor <= 10 ^ 18) lcm_factors;
}.

(** ** Correctness *)

(** [@requirement] [@short must count sequences with the
    specified GCD and LCM.] The answer: the number of
    such sequences, modulo 10^9 + 7. *)
Definition atrivialpursuit_spec (term_count : N)
    (gcd_factors lcm_factors : list N)
      (output : N) : Prop :=
  exists sequence_count,
    num_sequences term_count (prod gcd_factors)
      (prod lcm_factors)
      sequence_count /\
    output = sequence_count mod (10 ^ 9 + 7).

(** ** Interface *)

(** The machine-level interface.
    - Input [term_count]:
    - Input [gcd_factors]:
    - Input [lcm_factors]:
    - Output [output]: *)
Program atrivialpursuit : uint -> array uint -> array uint
  -> uint.

(** ** Bridge *)

(** [@requirement atrivialpursuit_spec] [@fold full
    correctness statement] On valid represented inputs,
    the program returns a represented output satisfying
    [atrivialpursuit_spec]. *)
Specification atrivialpursuit_correct :
  forall (term_count : N) (gcd_factors lcm_factors : list N)
         (term_count_int : uint)
           (gcd_factors_arr lcm_factors_arr : array uint),
  valid_input term_count gcd_factors lcm_factors ->
  repr term_count_int term_count ->
  repr gcd_factors_arr gcd_factors
    -> repr lcm_factors_arr lcm_factors ->
  exists output : N,
    repr (atrivialpursuit term_count_int gcd_factors_arr
      lcm_factors_arr)
      output /\
    atrivialpursuit_spec term_count gcd_factors lcm_factors
      output.

(** [@hide] The kernel primitives (int, array, float,
    string) and their axioms. *)
Allowed Primitive Axioms.
