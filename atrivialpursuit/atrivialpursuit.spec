(** * A Trivial Pursuit *)

(** ** Description *)

(** Count ordered sequences of positive integers with a specified length,
    greatest common divisor and least common multiple. The latter two are
    given as products of factors; return the count modulo $10^{9} + 7$.

    [@kattis atrivialpursuit]
    - Difficulty: 9.1
    - CPU time limit: 4 seconds
    - Memory limit: 1024 MB

    **Kattis Bounds**
    - Sequence length: $1 \le P \le 10^{18}$.
    - Each factor list has entry count $1 \le n \le 400$; each factor: $1 \le f_i \le 10^{18}$. *)

(** ** Examples *)

(** - Input convention: Sequence length and two factor counts, followed by the factors of the required GCD and LCM.
    - Output convention: The number of qualifying sequences modulo $10^9 + 7$. *)
(* Input:
3 1 2
3
17 18
Output:
216
*)

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
From StdGalilei Require Import repr.
Import ListNotations.
Open Scope N_scope.

(* G and L can have 400 * 18 digits: they exist
  only here, as
   [N]; every input and the answer fit in a [uint]. *)

(** ** Definitions *)

(** The number of elements of [l]. *)
Definition len {A} (l : list A) : N :=
  N.of_nat (List.length l).

(** The product of the elements of [l], with value one for the empty list. *)
Fixpoint prod (l : list N) : N :=
  match l with
  | [] => 1
  | term :: rest => term * prod rest
  end.

(** The greatest common divisor of the sequence. *)
Fixpoint seq_gcd (terms : list N) : N :=
  match terms with
  | [] => 0
  | term :: rest => N.gcd term (seq_gcd rest)
  end.
(** The least common multiple of the sequence. *)
Fixpoint seq_lcm (terms : list N) : N :=
  match terms with
  | [] => 1
  | term :: rest => N.lcm term (seq_lcm rest)
  end.

(** [terms] contains [term_count] positive integers with greatest common divisor
    [target_gcd] and least common multiple [target_lcm]. *)
Definition is_sequence
  (term_count target_gcd target_lcm : N)
    (terms : list N) : Prop :=
  len terms = term_count /\ Forall
    (fun term => 0 < term) terms /\
  seq_gcd terms = target_gcd /\ seq_lcm terms = target_lcm.

(** Exactly [sequence_count] distinct ordered sequences satisfy [is_sequence]. *)
Definition num_sequences
  (term_count target_gcd target_lcm sequence_count
    : N) : Prop :=
  exists sequences : list (list N),
    NoDup sequences /\
    (forall terms, In terms sequences <->
       is_sequence term_count target_gcd target_lcm terms)
         /\
    len sequences = sequence_count.

(** [@inside atrivialpursuit_correct] Input constraints based on the Kattis problem bounds, within which the implementation's correctness is guaranteed. *)
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

(** [@requirement]
    The output counts ordered sequences with the specified length, GCD and LCM, modulo
    $10^9 + 7$. *)
Definition atrivialpursuit_spec (term_count : N)
    (gcd_factors lcm_factors : list N)
      (output : N) : Prop :=
  exists sequence_count,
    num_sequences term_count (prod gcd_factors)
      (prod lcm_factors)
      sequence_count /\
    output = sequence_count mod (10 ^ 9 + 7).

(** ** Interface *)

(** Count ordered sequences of positive integers with a specified length, greatest common
    divisor and least common multiple. The latter two are given as products of factors;
    return the count modulo $10^{9} + 7$.
    - Input [term_count]: Required sequence length.
    - Input [gcd_factors]: Factors whose product is the required greatest common divisor.
    - Input [lcm_factors]: Factors whose product is the required least common multiple.
    - Output [output]: The output counts ordered sequences with the specified length, GCD and LCM, modulo $10^9 + 7$. *)
Program atrivialpursuit : uint -> array uint -> array uint
  -> uint.

(** [@example atrivialpursuit]
    - Sample: 1
    - Input [term_count]: 3
    - Input [gcd_factors]: [3]
    - Input [lcm_factors]: [17; 18]
    - Output [output]: 216
*)

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
