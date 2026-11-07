
(** val add : Uint63.t -> Uint63.t -> Uint63.t **)

let add = Uint63.add

(** val sub : Uint63.t -> Uint63.t -> Uint63.t **)

let sub = Uint63.sub

(** val eqb : Uint63.t -> Uint63.t -> bool **)

let eqb = Uint63.equal

(** val ltb : Uint63.t -> Uint63.t -> bool **)

let ltb = Uint63.lt

(** val lesb : Uint63.t -> Uint63.t -> bool **)

let lesb = Uint63.les

(** val make : Uint63.t -> 'a1 -> 'a1 Marray.t **)

let make = Marray.make

(** val get : 'a1 Marray.t -> Uint63.t -> 'a1 **)

let get = Marray.get

(** val set : 'a1 Marray.t -> Uint63.t -> 'a1 -> 'a1 Marray.t **)

let set = Marray.set

(** val length : 'a1 Marray.t -> Uint63.t **)

let length = Marray.length

type uint = Uint63.t

type sint = Uint63.t

(** val bdec : bool -> bool **)

let bdec = function
| true -> true
| false -> false

(** val iota_loop :
    Uint63.t -> Uint63.t -> Uint63.t Marray.t -> Uint63.t Marray.t **)

let rec iota_loop m i a =
  if bdec (ltb i m)
  then iota_loop m (add i (Uint63.of_int (1))) (set a i i)
  else a

(** val iota : Uint63.t -> Uint63.t Marray.t **)

let iota m =
  iota_loop m (Uint63.of_int (0)) (make m (Uint63.of_int (0)))

(** val merge_loop :
    Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t ->
    Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t Marray.t ->
    Uint63.t Marray.t **)

let rec merge_loop ws src iend jend kend i j k dst =
  if bdec (ltb k kend)
  then if if ltb i iend
          then if ltb j jend
               then lesb (get ws (get src i)) (get ws (get src j))
               else true
          else false
       then merge_loop ws src iend jend kend (add i (Uint63.of_int (1))) j
              (add k (Uint63.of_int (1))) (set dst k (get src i))
       else merge_loop ws src iend jend kend i (add j (Uint63.of_int (1)))
              (add k (Uint63.of_int (1))) (set dst k (get src j))
  else dst

(** val step_end : Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t **)

let step_end m w x =
  if ltb w (sub m x) then add x w else m

(** val pass_loop :
    Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t ->
    Uint63.t -> Uint63.t Marray.t -> Uint63.t Marray.t **)

let rec pass_loop ws src m w lo dst =
  if bdec (ltb lo m)
  then let mid = step_end m w lo in
       let hi = step_end m w mid in
       if bdec (ltb lo hi)
       then pass_loop ws src m w hi
              (merge_loop ws src mid hi hi lo mid lo dst)
       else dst
  else dst

(** val sort_loop :
    Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t Marray.t ->
    Uint63.t Marray.t -> Uint63.t Marray.t **)

let rec sort_loop ws m w src dst =
  if bdec (ltb w m)
  then if bdec (ltb w (add w w))
       then sort_loop ws m (add w w)
              (pass_loop ws src m w (Uint63.of_int (0)) dst) src
       else src
  else src

(** val sort_edges : Uint63.t Marray.t -> Uint63.t -> Uint63.t Marray.t **)

let sort_edges ws m =
  sort_loop ws m (Uint63.of_int (1)) (iota m) (make m (Uint63.of_int (0)))

(** val find :
    Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t **)

let rec find par rk v =
  let u = get par v in
  if eqb u v
  then v
  else if bdec (ltb (get rk v) (get rk u)) then find par rk u else v

(** val findr :
    Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t **)

let findr =
  find

(** val scan :
    Uint63.t -> Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t Marray.t
    -> Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t Marray.t ->
    Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t ->
    (Uint63.t * Uint63.t Marray.t) option **)

let rec scan n us vs ws ord m q par rk out cnt cost =
  if bdec (ltb q m)
  then let e = get ord q in
       let a = findr par rk (get us e) in
       let b = findr par rk (get vs e) in
       if eqb a b
       then scan n us vs ws ord m (add q (Uint63.of_int (1))) par rk out cnt
              cost
       else let ra = get rk a in
            let rb = get rk b in
            if ltb ra rb
            then scan n us vs ws ord m (add q (Uint63.of_int (1)))
                   (set par a b) rk (set out cnt e)
                   (add cnt (Uint63.of_int (1))) (add cost (get ws e))
            else if ltb rb ra
                 then scan n us vs ws ord m (add q (Uint63.of_int (1)))
                        (set par b a) rk (set out cnt e)
                        (add cnt (Uint63.of_int (1))) (add cost (get ws e))
                 else scan n us vs ws ord m (add q (Uint63.of_int (1)))
                        (set par a b) (set rk b (add rb (Uint63.of_int (1))))
                        (set out cnt e) (add cnt (Uint63.of_int (1)))
                        (add cost (get ws e))
  else if eqb cnt (sub n (Uint63.of_int (1))) then Some (cost, out) else None

(** val mst_impl :
    Uint63.t -> Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t Marray.t
    -> (Uint63.t * Uint63.t Marray.t) option **)

let mst_impl n us vs ws =
  let m = length us in
  scan n us vs ws (sort_edges ws m) m (Uint63.of_int (0)) (iota n)
    (make n (Uint63.of_int (0)))
    (make (sub n (Uint63.of_int (1))) (Uint63.of_int (0)))
    (Uint63.of_int (0)) (Uint63.of_int (0))

module MinspantreeImpl =
 struct
  (** val mst :
      uint -> uint Marray.t -> uint Marray.t -> sint Marray.t -> (sint * uint
      Marray.t) option **)

  let mst =
    mst_impl
 end
