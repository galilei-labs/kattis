(* Mutable-array runtime, copied from the public Cold extraction runtime
   (code unchanged; historical benchmark commentary omitted).
   UNSOUND IN GENERAL: set mutates its input. Correctness requires linear
   array use, which this extraction route does not verify.
   Out-of-range get returns the default; out-of-range set is the identity. *)

type 'a t = { data : 'a array; def : 'a }

let max_array_length32 = 4194303

let max_length = Uint63.of_int max_array_length32

let length_to_int i = snd (Uint63.to_int2 i) [@@inline always]

let trunc_size n =
  if Uint63.le Uint63.zero n && Uint63.lt n (Uint63.of_int max_array_length32)
  then length_to_int n
  else max_array_length32

let make n def = { data = Array.make (trunc_size n) def; def } [@@inline always]

let length p = Uint63.of_int (Array.length p.data) [@@inline always]

let get p n =
  let l = Array.length p.data in
  if Uint63.le Uint63.zero n && Uint63.lt n (Uint63.of_int l)
  then Array.unsafe_get p.data (length_to_int n)
  else p.def
  [@@inline always]

let set p n e =
  let l = Array.length p.data in
  if Uint63.le Uint63.zero n && Uint63.lt n (Uint63.of_int l)
  then Array.unsafe_set p.data (length_to_int n) e;
  p
  [@@inline always]

let default p = p.def [@@inline always]

let copy p = { data = Array.copy p.data; def = p.def }

(* Harness helpers, same names and meaning as Parray's. *)

let of_array a def = { data = Array.copy a; def }

let to_array p = (Array.copy p.data, p.def)
