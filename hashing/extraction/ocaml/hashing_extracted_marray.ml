
(** val lsl0 : Uint63.t -> Uint63.t -> Uint63.t **)

let lsl0 = Uint63.l_sl

(** val lsr0 : Uint63.t -> Uint63.t -> Uint63.t **)

let lsr0 = Uint63.l_sr

(** val land0 : Uint63.t -> Uint63.t -> Uint63.t **)

let land0 = Uint63.l_and

(** val add : Uint63.t -> Uint63.t -> Uint63.t **)

let add = Uint63.add

(** val sub : Uint63.t -> Uint63.t -> Uint63.t **)

let sub = Uint63.sub

(** val mulc : Uint63.t -> Uint63.t -> Uint63.t * Uint63.t **)

let mulc = Uint63.mulc

(** val ltb : Uint63.t -> Uint63.t -> bool **)

let ltb = Uint63.lt

(** val leb : Uint63.t -> Uint63.t -> bool **)

let leb = Uint63.le

(** val make : Uint63.t -> 'a1 -> 'a1 Marray.t **)

let make = Marray.make

(** val get : 'a1 Marray.t -> Uint63.t -> 'a1 **)

let get = Marray.get

(** val set : 'a1 Marray.t -> Uint63.t -> 'a1 -> 'a1 Marray.t **)

let set = Marray.set

(** val length : 'a1 Marray.t -> Uint63.t **)

let length = Marray.length

type char63 = Uint63.t

type string = Pstring.t

(** val length0 : string -> Uint63.t **)

let length0 = Pstring.length

(** val get0 : string -> Uint63.t -> char63 **)

let get0 = Pstring.get

type uint = Uint63.t

(** val p61 : Uint63.t **)

let p61 =
  (Uint63.of_int (2305843009213693951))

(** val mulmod : Uint63.t -> Uint63.t -> Uint63.t **)

let mulmod a b =
  let (h, l) = mulc a b in
  let s =
    add (add (lsl0 h (Uint63.of_int (2))) (lsr0 l (Uint63.of_int (61))))
      (land0 l p61)
  in
  let t = add (lsr0 s (Uint63.of_int (61))) (land0 s p61) in
  if leb p61 t then sub t p61 else t

(** val addmod : Uint63.t -> Uint63.t -> Uint63.t **)

let addmod a b =
  let s = add a b in if leb p61 s then sub s p61 else s

(** val submod : Uint63.t -> Uint63.t -> Uint63.t **)

let submod a b =
  if leb b a then sub a b else sub (add a p61) b

(** val bdec : bool -> bool **)

let bdec = function
| true -> true
| false -> false

(** val pre_loop :
    Uint63.t -> string -> Uint63.t -> Uint63.t -> Uint63.t Marray.t ->
    Uint63.t -> Uint63.t Marray.t **)

let rec pre_loop r s n i t acc =
  if bdec (ltb i n)
  then let acc' = addmod (mulmod acc r) (get0 s i) in
       pre_loop r s n (add i (Uint63.of_int (1)))
         (set t (add i (Uint63.of_int (1))) acc') acc'
  else t

(** val pow_loop :
    Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t Marray.t -> Uint63.t ->
    Uint63.t Marray.t **)

let rec pow_loop r n i t acc =
  if bdec (ltb i n)
  then let acc' = mulmod acc r in
       pow_loop r n (add i (Uint63.of_int (1)))
         (set t (add i (Uint63.of_int (1))) acc') acc'
  else t

(** val prefix_hashes :
    Uint63.t -> string -> Uint63.t -> Uint63.t Marray.t **)

let prefix_hashes r s n =
  pre_loop r s n (Uint63.of_int (0))
    (make (add n (Uint63.of_int (1))) (Uint63.of_int (0))) (Uint63.of_int (0))

(** val powers : Uint63.t -> Uint63.t -> Uint63.t Marray.t **)

let powers r n =
  pow_loop r n (Uint63.of_int (0))
    (make (add n (Uint63.of_int (1))) (Uint63.of_int (1))) (Uint63.of_int (1))

(** val hash :
    Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t **)

let hash pre pw l r =
  let k = get pw (sub r l) in
  addmod (submod (get pre r) (mulmod (get pre l) k)) k

(** val q_loop :
    Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t
    Marray.t -> Uint63.t -> Uint63.t -> Uint63.t Marray.t -> Uint63.t Marray.t **)

let rec q_loop pre pw xl xr q j out =
  if bdec (ltb j q)
  then q_loop pre pw xl xr q (add j (Uint63.of_int (1)))
         (set out j (hash pre pw (get xl j) (get xr j)))
  else out

(** val hashes_impl :
    uint -> string -> uint Marray.t -> uint Marray.t -> uint Marray.t **)

let hashes_impl r s xl xr =
  let n = length0 s in
  let pre = prefix_hashes r s n in
  let pw = powers r n in
  let q = length xl in
  q_loop pre pw xl xr q (Uint63.of_int (0)) (make q (Uint63.of_int (0)))

(** val hashes :
    uint -> string -> uint Marray.t -> uint Marray.t -> uint Marray.t **)

let hashes =
  hashes_impl
