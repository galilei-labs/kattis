(* @function        pascal
   @signature       uint -> uint
   @math_signature  N -> N
   @summary         [pascal n] is what Frane's Pascal program prints on
                    input n: the counter after the loop "for i := n-1
                    downto 1, add one to the counter, stop as soon as
                    n mod i = 0".
*)

From Stdlib Require Import ZArith NArith List Uint63 PArray.
From Respeced Require Import Repr.
Import ListNotations.
Open Scope N_scope.

(* Math side.  Frane's program, line by line:

     readln(N);
     counter := 0;
     for i := N - 1 downto 1 do begin
       counter := counter + 1;
       if N mod i = 0 then break;
     end;
     writeln(counter);                                                    *)

(* [frane_loop n i counter]: the loop run from the current value i of the
   loop variable down to 1, the counter being [counter] on entry; it
   returns the counter on exit (after the break, or after i = 1). *)
Fixpoint frane_loop (n : N) (i : nat) (counter : N) : N :=
  match i with
  | O => counter
  | S i' =>
      let counter' := counter + 1 in
      if n mod N.of_nat i =? 0 then counter' else frane_loop n i' counter'
  end.

(* readln(N); counter := 0; the loop from N - 1; writeln(counter). *)
Definition frane_output (n : N) : N :=
  frane_loop n (N.to_nat (n - 1)) 0.

(* The statement's bounds. *)
Record valid_input (n : N) : Prop := {
  (* The first and only line of input contains the integer 1 <= N <= 10^9. *)
  vi_n : 1 <= n <= 10 ^ 9;
}.

(* The answer is the output of Frane's program. *)
Definition pascal_spec (n c : N) : Prop :=
  c = frane_output n.

Program pascal : uint -> uint.

Specification pascal_correct : forall (n : N) (x : uint),
  valid_input n -> repr x n ->
  exists c : N, repr (pascal x) c /\ pascal_spec n c.

(* The kernel primitives (int, array, float, string) and their axioms. *)
Allowed Primitive Axioms.
