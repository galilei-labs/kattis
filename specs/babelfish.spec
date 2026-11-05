(* @function        babelfish
   @signature       array PrimString.string -> array PrimString.string ->
                    array PrimString.string -> array (option PrimString.string)
   @math_signature  list string -> list string -> list string ->
                    list (option string)
   @summary         [babelfish english foreign message] translates the message
                    word by word with the dictionary whose i-th entry pairs the
                    English word english[i] with the foreign word foreign[i]:
                    the k-th answer is Some w when message[k] is a foreign word
                    of the dictionary and w its English word, and None (printed
                    "eh") when message[k] is not in the dictionary.
*)

From Stdlib Require Import ZArith NArith List Uint63 PArray.
From Stdlib Require PrimString.
From Stdlib Require Import String Ascii.
From Respeced Require Import Repr.
Import ListNotations.
Open Scope N_scope.

(* Math side.  The dictionary lines "english foreign" are two parallel lists,
   one per column. *)

(* The number of elements of l. *)
Definition len {A} (l : list A) : N := N.of_nat (List.length l).

(* The i-th element of l, if any. *)
Definition at_ {A} (l : list A) (i : N) : option A := nth_error l (N.to_nat i).

(* A word of the input: a non-empty sequence of at most 10 lowercase letters
   (character codes 97 'a' to 122 'z'). *)
Definition word (s : string) : Prop :=
  1 <= N.of_nat (String.length s) <= 10 /\
  forall k c, String.get k s = Some c -> 97 <= N_of_ascii c <= 122.

(* Some dictionary entry pairs the foreign word x with the English word w. *)
Definition translates (english foreign : list string) (x w : string) : Prop :=
  exists i, at_ foreign i = Some x /\ at_ english i = Some w.

(* The statement's guarantees, for the one test case. *)
Record valid_input (english foreign message : list string) : Prop := {
  (* each dictionary entry is a line containing an English word, followed by
     a space and a foreign language word *)
  vi_entries : len english = len foreign;
  (* up to 100 000 dictionary entries *)
  vi_dict_length : len foreign <= 100000;
  (* a message of up to 100 000 words *)
  vi_message_length : len message <= 100000;
  (* each word in the input is a non-empty sequence of at most 10 lowercase
     letters *)
  vi_english_words : Forall word english;
  vi_foreign_words : Forall word foreign;
  vi_message_words : Forall word message;
  (* no foreign word appears more than once in the dictionary *)
  vi_distinct : NoDup foreign;
}.

(* The answer for the foreign word x: Some w exactly when the dictionary
   translates x as w, so None exactly when x is not in the dictionary. *)
Definition answer (english foreign : list string) (x : string)
    (o : option string) : Prop :=
  forall w, o = Some w <-> translates english foreign x w.

(* One answer per message word, in order. *)
Definition babelfish_spec (english foreign message : list string)
    (out : list (option string)) : Prop :=
  Forall2 (answer english foreign) message out.

Program babelfish :
  array PrimString.string -> array PrimString.string ->
  array PrimString.string -> array (option PrimString.string).

Specification babelfish_correct :
  forall (english foreign message : list string)
         (e f m : array PrimString.string),
  valid_input english foreign message ->
  repr e english -> repr f foreign -> repr m message ->
  exists out : list (option string),
    repr (babelfish e f m) out /\ babelfish_spec english foreign message out.

(* The kernel primitives (int, array, float, string) and their axioms. *)
Allowed Primitive Axioms.
