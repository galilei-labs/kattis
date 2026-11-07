
(** val fst : ('a1 * 'a2) -> 'a1 **)

let fst = function
| (x, _) -> x

(** val snd : ('a1 * 'a2) -> 'a2 **)

let snd = function
| (_, y) -> y

(** val add : Uint63.t -> Uint63.t -> Uint63.t **)

let add = Uint63.add

(** val sub : Uint63.t -> Uint63.t -> Uint63.t **)

let sub = Uint63.sub

(** val div : Uint63.t -> Uint63.t -> Uint63.t **)

let div = Uint63.div

(** val eqb : Uint63.t -> Uint63.t -> bool **)

let eqb = Uint63.equal

(** val ltb : Uint63.t -> Uint63.t -> bool **)

let ltb = Uint63.lt

(** val make : Uint63.t -> 'a1 -> 'a1 Marray.t **)

let make = Marray.make

(** val get : 'a1 Marray.t -> Uint63.t -> 'a1 **)

let get = Marray.get

(** val set : 'a1 Marray.t -> Uint63.t -> 'a1 -> 'a1 Marray.t **)

let set = Marray.set

(** val length : 'a1 Marray.t -> Uint63.t **)

let length = Marray.length

type string = Pstring.t

(** val cat : string -> string -> string **)

let cat = Pstring.cat

type uint = Uint63.t

(** val bdec : bool -> bool **)

let bdec = function
| true -> true
| false -> false

(** val split_ok : Uint63.t -> Uint63.t -> bool **)

let split_ok lo hi =
  (&&) (ltb lo hi) (ltb (Uint63.of_int (1)) (sub hi lo))

(** val mid_of : Uint63.t -> Uint63.t -> Uint63.t **)

let mid_of lo hi =
  add lo (div (sub hi lo) (Uint63.of_int (2)))

(** val init_loop :
    Uint63.t -> Uint63.t -> Uint63.t Marray.t -> Uint63.t Marray.t **)

let rec init_loop n k tl =
  if bdec (ltb k n)
  then init_loop n (add k (Uint63.of_int (1))) (set tl k k)
  else tl

(** val ops_loop :
    Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t ->
    Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t Marray.t * Uint63.t
    Marray.t **)

let rec ops_loop xa xb m k nx tl =
  if bdec (ltb k m)
  then let x = sub (get xa k) (Uint63.of_int (1)) in
       let y = sub (get xb k) (Uint63.of_int (1)) in
       let ty = get tl y in
       let tx = get tl x in
       ops_loop xa xb m (add k (Uint63.of_int (1))) (set nx tx y)
         (set tl x ty)
  else (nx, tl)

(** val walk :
    Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t ->
    Uint63.t Marray.t -> Uint63.t Marray.t * Uint63.t **)

let rec walk nx t n cur i ord =
  if bdec (ltb i n)
  then if eqb cur t
       then ((set ord i cur), (add i (Uint63.of_int (1))))
       else walk nx t n (get nx cur) (add i (Uint63.of_int (1)))
              (set ord i cur)
  else (ord, i)

(** val build :
    string Marray.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t -> string **)

let rec build xs ord lo hi =
  if bdec (split_ok lo hi)
  then cat (build xs ord lo (mid_of lo hi)) (build xs ord (mid_of lo hi) hi)
  else get xs (get ord lo)

(** val root_of : Uint63.t Marray.t -> Uint63.t -> Uint63.t **)

let root_of xa m =
  if eqb m (Uint63.of_int (0))
  then (Uint63.of_int (0))
  else sub (get xa (sub m (Uint63.of_int (1)))) (Uint63.of_int (1))

(** val joinstrings_impl :
    string Marray.t -> uint Marray.t -> uint Marray.t -> string **)

let joinstrings_impl xs xa xb =
  let n = length xs in
  let m = length xa in
  let tl0 = init_loop n (Uint63.of_int (0)) (make n (Uint63.of_int (0))) in
  let nt =
    ops_loop xa xb m (Uint63.of_int (0)) (make n (Uint63.of_int (0))) tl0
  in
  let nx = fst nt in
  let tl = snd nt in
  let r = root_of xa m in
  let oc =
    walk nx (get tl r) n r (Uint63.of_int (0)) (make n (Uint63.of_int (0)))
  in
  build xs (fst oc) (Uint63.of_int (0)) (snd oc)

module JoinstringsImpl =
 struct
  (** val joinstrings :
      string Marray.t -> uint Marray.t -> uint Marray.t -> string **)

  let joinstrings =
    joinstrings_impl
 end
