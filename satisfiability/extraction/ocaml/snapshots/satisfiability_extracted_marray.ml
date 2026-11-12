
(** val negb : bool -> bool **)

let negb = function
| true -> false
| false -> true

(** val lsl0 : Uint63.t -> Uint63.t -> Uint63.t **)

let lsl0 = Uint63.l_sl

(** val land0 : Uint63.t -> Uint63.t -> Uint63.t **)

let land0 = Uint63.l_and

(** val lor0 : Uint63.t -> Uint63.t -> Uint63.t **)

let lor0 = Uint63.l_or

(** val add : Uint63.t -> Uint63.t -> Uint63.t **)

let add = Uint63.add

(** val sub : Uint63.t -> Uint63.t -> Uint63.t **)

let sub = Uint63.sub

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

type uint = Uint63.t

type 'a literal =
| X of 'a
| NotX of 'a

(** val bdec : bool -> bool **)

let bdec = function
| true -> true
| false -> false

(** val bitof : Uint63.t -> Uint63.t **)

let bitof v =
  lsl0 (Uint63.of_int (1)) (sub v (Uint63.of_int (1)))

(** val lit_bits : bool -> uint literal -> Uint63.t **)

let lit_bits s = function
| X v -> if s then bitof v else (Uint63.of_int (0))
| NotX v -> if s then (Uint63.of_int (0)) else bitof v

(** val mask_loop :
    bool -> uint literal Marray.t -> Uint63.t -> Uint63.t -> Uint63.t ->
    Uint63.t **)

let rec mask_loop s c len i acc =
  if bdec (ltb i len)
  then mask_loop s c len (add i (Uint63.of_int (1)))
         (lor0 acc (lit_bits s (get c i)))
  else acc

(** val clause_mask : bool -> uint literal Marray.t -> Uint63.t **)

let clause_mask s c =
  mask_loop s c (length c) (Uint63.of_int (0)) (Uint63.of_int (0))

(** val fill_loop :
    bool -> uint literal Marray.t Marray.t -> Uint63.t -> Uint63.t ->
    Uint63.t Marray.t -> Uint63.t Marray.t **)

let rec fill_loop s y m k r =
  if bdec (ltb k m)
  then fill_loop s y m (add k (Uint63.of_int (1)))
         (set r k (clause_mask s (get y k)))
  else r

(** val masks :
    bool -> uint literal Marray.t Marray.t -> Uint63.t Marray.t **)

let masks s y =
  fill_loop s y (length y) (Uint63.of_int (0))
    (make (length y) (Uint63.of_int (0)))

(** val clause_ok : Uint63.t -> Uint63.t -> Uint63.t -> bool **)

let clause_ok t p q =
  if eqb (land0 p t) (Uint63.of_int (0))
  then negb (eqb (land0 q t) q)
  else true

(** val check_loop :
    Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t ->
    Uint63.t -> bool **)

let rec check_loop pos neg m k t =
  if bdec (ltb k m)
  then if clause_ok t (get pos k) (get neg k)
       then check_loop pos neg m (add k (Uint63.of_int (1))) t
       else false
  else true

(** val check_all :
    Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t -> bool **)

let check_all pos neg m t =
  check_loop pos neg m (Uint63.of_int (0)) t

(** val search_loop :
    Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t ->
    Uint63.t -> bool **)

let rec search_loop pos neg m lim t =
  if bdec (ltb t lim)
  then if check_all pos neg m t
       then true
       else search_loop pos neg m lim (add t (Uint63.of_int (1)))
  else false

(** val satisfiable_impl :
    Uint63.t -> uint literal Marray.t Marray.t -> bool **)

let satisfiable_impl n y =
  let m = length y in
  let lim = lsl0 (Uint63.of_int (1)) n in
  search_loop (masks true y) (masks false y) m lim (Uint63.of_int (0))

(** val satisfiable : uint -> uint literal Marray.t Marray.t -> bool **)

let satisfiable =
  satisfiable_impl
