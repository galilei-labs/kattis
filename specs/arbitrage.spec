(* @function        arbitrage
   @signature       uint -> array uint -> array uint -> array uint -> array uint -> bool
   @math_signature  N -> list N -> list N -> list N -> list N -> bool
   @summary         One test case of "Arbitrage?": [c] currencies and the
                    exchange rates k (pay a_k units of currency src_k, get
                    b_k units of currency dst_k).  The answer is true
                    ("Arbitrage") exactly when some sequence of exchanges,
                    starting and ending in the same currency, turns a positive
                    amount into a strictly larger one, amounts computed exactly
                    over the rationals; false ("Ok") otherwise.
*)

From Stdlib Require Import ZArith NArith QArith List Uint63 PArray.
From Respeced Require Import Repr.
Import ListNotations.
Open Scope N_scope.

(* Math side.  A currency is its 0-based position in the line of codes (the
   codes of one test case are different); a rate is the k-th entry of four
   parallel lists, the columns of the input line "src dst A:B". *)

(* The number of elements of l. *)
Definition len {A} (l : list A) : N := N.of_nat (List.length l).

(* The k-th element of l (0 beyond the end, never read there). *)
Definition get (l : list N) (k : N) : N := nth (N.to_nat k) l 0.

(* Performing the exchanges ks in order leads from currency u to currency v:
   each one is paid in the currency the previous one produced. *)
Fixpoint leads (src dst : list N) (u v : N) (ks : list N) : Prop :=
  match ks with
  | [] => u = v
  | k :: ks' => get src k = u /\ leads src dst (get dst k) v ks'
  end.

(* The amount held after the exchanges ks, starting from x units:
   paying x units at rate A:B gives x * B / A units. *)
Fixpoint amount_after (a b : list N) (ks : list N) (x : Q) : Q :=
  match ks with
  | [] => x
  | k :: ks' =>
      amount_after a b ks'
        (x * (inject_Z (Z.of_N (get b k)) / inject_Z (Z.of_N (get a k))))%Q
  end.

(* Some nonempty sequence of available exchanges, from a currency back to
   itself, ends with strictly more than a positive starting amount. *)
Definition profitable (src dst a b : list N) : Prop :=
  exists (u : N) (ks : list N) (x : Q),
    ks <> [] /\
    Forall (fun k => k < len src) ks /\
    leads src dst u u ks /\
    (0 < x)%Q /\ (x < amount_after a b ks x)%Q.

(* The statement's bounds, for one test case. *)
Record valid_input (c : N) (src dst a b : list N) : Prop := {
  (* one positive integer number C, 1 <= C <= 200, the number of currencies *)
  vi_c : 1 <= c <= 200;
  (* R, 0 <= R <= C * (C - 1), the number of exchange rates; each rate line
     gives a first code, a second code, A_i and B_i *)
  vi_r : len src <= c * (c - 1);
  vi_dst_len : len dst = len src;
  vi_a_len : len a = len src;
  vi_b_len : len b = len src;
  (* each code of a rate is one of the C currency codes of the test case *)
  vi_src : Forall (fun u => u < c) src;
  vi_dst : Forall (fun v => v < c) dst;
  (* the two currencies are different *)
  vi_diff : forall k, k < len src -> get src k <> get dst k;
  (* 1 <= A_i, B_i <= 100 *)
  vi_a : Forall (fun x => 1 <= x <= 100) a;
  vi_b : Forall (fun x => 1 <= x <= 100) b;
}.

(* "Arbitrage" (true) exactly when some exchange sequence gives a profit. *)
Definition arbitrage_spec (c : N) (src dst a b : list N) (o : bool) : Prop :=
  o = true <-> profitable src dst a b.

Program arbitrage :
  uint -> array uint -> array uint -> array uint -> array uint -> bool.

Specification arbitrage_correct :
  forall (c : N) (src dst a b : list N)
         (xc : uint) (xsrc xdst xa xb : array uint),
  valid_input c src dst a b ->
  repr xc c -> repr xsrc src -> repr xdst dst -> repr xa a -> repr xb b ->
  exists o : bool, repr (arbitrage xc xsrc xdst xa xb) o /\
                   arbitrage_spec c src dst a b o.

(* The kernel primitives (int, array, float, string) and their axioms. *)
Allowed Primitive Axioms.

(* The four classical axioms Stdlib's reals rest on: the math side is not over R, but an accepted implementation proves through Stdlib's reals (decision of 2026-10-23). *)
Allowed Axioms ClassicalDedekindReals.sig_forall_dec ClassicalDedekindReals.sig_not_dec Classical_Prop.classic FunctionalExtensionality.functional_extensionality_dep.
