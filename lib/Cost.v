(* Cost : stating a bound on the number of steps of a machine function, in
   a spec's Module Type, in two lines :

     Elpi speck_complexity_parameter parameter f_cost f.
     Parameter f_time : exists c, forall x y, cost2 f_cost x y <= c * size x.

   The first line declares f_cost, the cost translation of f (its type is
   computed from f's signature by rocq-speck's command) ; the second bounds
   it.  The translation (vendored in rocq-speck, library Complexity) is
   value-indexed : f_cost takes, with each argument, a witness of that
   argument's structure.  For the machine types of this repository (int,
   float, PrimString.string and arrays of them) the witness is a single
   constructor with no content, so cost1 / cost2 / cost3 fill it in and
   fix the cost monoid to stepsCM, the step counter : one step per
   function application, per match, per unfolding of a fix and per
   primitive operation ; constructors, variables and proofs are free.

   Written 2026-10-26 for complexity/ ; meant for lib/ once the
   repository builds under Rocq 9.2 (the translation needs 9.2). *)

From Stdlib Require Import ZArith Uint63 PArray Floats.
From Stdlib Require PrimString.
From Complexity Require Export Spec Speck.
From Respeced Require Import Repr.

(* option appears in machine signatures ; bool, nat, list, prod and the
   primitive types are translated by the library. *)
Elpi complexity option.

(* ====================================================================== *)
(* The witness of a machine value, trivial for the primitive types.       *)
(* ====================================================================== *)

Class Witness (A : Type) (AC : costMonoid -> A -> Type) :=
  witness : forall a : A, AC stepsCM a.

Instance witness_int : Witness int int_cost := int_val stepsCM.
Instance witness_uint : Witness uint int_cost := int_val stepsCM.
Instance witness_sint : Witness sint int_cost := int_val stepsCM.
Instance witness_float : Witness float float_cost := float_val stepsCM.
Instance witness_string : Witness PrimString.string string_cost := string_val stepsCM.
(* stated eta-expanded (fun CM t => ... t), the shape the translation gives
   an array argument's family: instance search does not match the
   eta-reduced form (found by the floatmax specer, 2026-10-26) *)
Instance witness_array A AC `{Witness A AC} :
  Witness (array A) (fun CM t => array_cost CM A (AC CM) t) :=
  fun t => array_val stepsCM A (AC stepsCM) t (fun i => witness t.[i]) (witness (default t)).
(* uint and sint are Typeclasses Opaque aliases of int (Repr.v, so that the
   repr instances tell them apart), and int_cost is typed over int: when the
   family is fixed in advance by the translation's type, as cost1 f_cost x
   fixes it, the generic instance does not match at A := sint (the mergesort
   specer, 2026-10-26); these two state the arrays of words directly. *)
Instance witness_array_uint : Witness (array uint) (fun CM t => array_cost CM uint (int_cost CM) t) :=
  @witness_array uint int_cost _.
Instance witness_array_sint : Witness (array sint) (fun CM t => array_cost CM sint (int_cost CM) t) :=
  @witness_array sint int_cost _.

(* ====================================================================== *)
(* The number of steps of a call, by arity.                               *)
(* ====================================================================== *)

(* f : A -> R, translated as forall CM a aC, CostM (R_cost (f a)). *)
Definition cost1 {A : Type} {AC : costMonoid -> A -> Type} `{Witness A AC}
  {C : forall CM (a : A), AC CM a -> Type}
  (fc : forall CM (a : A) (aC : AC CM a), CostM (C CM a aC))
  (a : A) : nat :=
  cost (fc stepsCM a (witness a)).

(* f : A -> B -> R, curried call-by-value : the cost of the first layer plus
   the cost of applying its value to the second argument (call_cost2). *)
Definition cost2 {A B : Type} {AC : costMonoid -> A -> Type} {BC : costMonoid -> B -> Type}
  `{Witness A AC} `{Witness B BC}
  {C : forall CM (a : A), AC CM a -> forall (b : B), BC CM b -> Type}
  (fc : forall CM (a : A) (aC : AC CM a),
        CostM (forall (b : B) (bC : BC CM b), CostM (C CM a aC b bC)))
  (a : A) (b : B) : nat :=
  call_cost2 (fc stepsCM) a (witness a) b (witness b).

(* f : A -> B -> D -> R. *)
Definition cost3 {A B D : Type}
  {AC : costMonoid -> A -> Type} {BC : costMonoid -> B -> Type} {DC : costMonoid -> D -> Type}
  `{Witness A AC} `{Witness B BC} `{Witness D DC}
  {C : forall CM (a : A), AC CM a -> forall (b : B), BC CM b -> forall (d : D), DC CM d -> Type}
  (fc : forall CM (a : A) (aC : AC CM a),
        CostM (forall (b : B) (bC : BC CM b),
               CostM (forall (d : D) (dC : DC CM d), CostM (C CM a aC b bC d dC))))
  (a : A) (b : B) (d : D) : nat :=
  call_cost3 (fc stepsCM) a (witness a) b (witness b) d (witness d).

(* f with four, five and six arguments (slowleak has six): the sum of the
   costs of the layers, as call_cost2/3 above (Steps.v has call_cost up to
   5; these are written out with extract, 2026-11-03).  Unfold them by
   `unfold cost6` in a proof. *)
Definition cost4 {A B D E : Type}
  {AC : costMonoid -> A -> Type} {BC : costMonoid -> B -> Type}
  {DC : costMonoid -> D -> Type} {EC : costMonoid -> E -> Type}
  `{Witness A AC} `{Witness B BC} `{Witness D DC} `{Witness E EC}
  {C : forall CM (a : A), AC CM a -> forall (b : B), BC CM b ->
       forall (d : D), DC CM d -> forall (e : E), EC CM e -> Type}
  (fc : forall CM (a : A) (aC : AC CM a),
        CostM (forall (b : B) (bC : BC CM b),
               CostM (forall (d : D) (dC : DC CM d),
                      CostM (forall (e : E) (eC : EC CM e), CostM (C CM a aC b bC d dC e eC)))))
  (a : A) (b : B) (d : D) (e : E) : nat :=
  let m1 := fc stepsCM a (witness a) in
  let m2 := extract m1 b (witness b) in
  let m3 := extract m2 d (witness d) in
  cost m1 + cost m2 + cost m3 + cost (extract m3 e (witness e)).

Definition cost5 {A B D E F : Type}
  {AC : costMonoid -> A -> Type} {BC : costMonoid -> B -> Type}
  {DC : costMonoid -> D -> Type} {EC : costMonoid -> E -> Type} {FC : costMonoid -> F -> Type}
  `{Witness A AC} `{Witness B BC} `{Witness D DC} `{Witness E EC} `{Witness F FC}
  {C : forall CM (a : A), AC CM a -> forall (b : B), BC CM b ->
       forall (d : D), DC CM d -> forall (e : E), EC CM e -> forall (f : F), FC CM f -> Type}
  (fc : forall CM (a : A) (aC : AC CM a),
        CostM (forall (b : B) (bC : BC CM b),
               CostM (forall (d : D) (dC : DC CM d),
                      CostM (forall (e : E) (eC : EC CM e),
                             CostM (forall (f : F) (fC : FC CM f), CostM (C CM a aC b bC d dC e eC f fC))))))
  (a : A) (b : B) (d : D) (e : E) (f : F) : nat :=
  let m1 := fc stepsCM a (witness a) in
  let m2 := extract m1 b (witness b) in
  let m3 := extract m2 d (witness d) in
  let m4 := extract m3 e (witness e) in
  cost m1 + cost m2 + cost m3 + cost m4 + cost (extract m4 f (witness f)).

Definition cost6 {A B D E F G : Type}
  {AC : costMonoid -> A -> Type} {BC : costMonoid -> B -> Type}
  {DC : costMonoid -> D -> Type} {EC : costMonoid -> E -> Type}
  {FC : costMonoid -> F -> Type} {GC : costMonoid -> G -> Type}
  `{Witness A AC} `{Witness B BC} `{Witness D DC} `{Witness E EC} `{Witness F FC} `{Witness G GC}
  {C : forall CM (a : A), AC CM a -> forall (b : B), BC CM b ->
       forall (d : D), DC CM d -> forall (e : E), EC CM e ->
       forall (f : F), FC CM f -> forall (g : G), GC CM g -> Type}
  (fc : forall CM (a : A) (aC : AC CM a),
        CostM (forall (b : B) (bC : BC CM b),
               CostM (forall (d : D) (dC : DC CM d),
                      CostM (forall (e : E) (eC : EC CM e),
                             CostM (forall (f : F) (fC : FC CM f),
                                    CostM (forall (g : G) (gC : GC CM g),
                                           CostM (C CM a aC b bC d dC e eC f fC g gC)))))))
  (a : A) (b : B) (d : D) (e : E) (f : F) (g : G) : nat :=
  let m1 := fc stepsCM a (witness a) in
  let m2 := extract m1 b (witness b) in
  let m3 := extract m2 d (witness d) in
  let m4 := extract m3 e (witness e) in
  let m5 := extract m4 f (witness f) in
  cost m1 + cost m2 + cost m3 + cost m4 + cost m5 + cost (extract m5 g (witness g)).

(* ====================================================================== *)
(* The size of a machine value, for the right-hand side of a bound.       *)
(* ====================================================================== *)

Class Size (A : Type) := size : A -> nat.

(* a number is its own size (sumto n runs in O(n)) *)
Instance size_int : Size int := fun x => Z.to_nat (Uint63.to_Z x).
Instance size_uint : Size uint := fun x => Z.to_nat (Uint63.to_Z x).
Instance size_string : Size PrimString.string := fun s => Z.to_nat (Uint63.to_Z (PrimString.length s)).
Instance size_array A : Size (array A) := fun t => Z.to_nat (Uint63.to_Z (PArray.length t)).
