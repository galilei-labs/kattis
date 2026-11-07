
(** val add : Uint63.t -> Uint63.t -> Uint63.t **)

let add = Uint63.add

(** val sub : Uint63.t -> Uint63.t -> Uint63.t **)

let sub = Uint63.sub

(** val eqb : Uint63.t -> Uint63.t -> bool **)

let eqb = Uint63.equal

(** val ltb : Uint63.t -> Uint63.t -> bool **)

let ltb = Uint63.lt

(** val ltsb : Uint63.t -> Uint63.t -> bool **)

let ltsb = Uint63.lts

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

type sint = Uint63.t

(** val bdec : bool -> bool **)

let bdec = function
| true -> true
| false -> false

(** val nEG : Uint63.t **)

let nEG =
  (Uint63.of_int (-4611686018427387904))

(** val mONE : Uint63.t **)

let mONE =
  (Uint63.of_int (-1))

(** val wt : string -> Uint63.t -> Uint63.t -> Uint63.t **)

let wt xs v v0 =
  if eqb v0 (Uint63.of_int (0))
  then (Uint63.of_int (0))
  else if eqb v0 (sub v (Uint63.of_int (1)))
       then (Uint63.of_int (0))
       else let c = get0 xs v0 in
            if eqb c (Uint63.of_int (88))
            then (Uint63.of_int (1))
            else if eqb c (Uint63.of_int (46))
                 then mONE
                 else (Uint63.of_int (0))

(** val cnt_loop :
    Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t Marray.t ->
    Uint63.t Marray.t **)

let rec cnt_loop xsrc e k c =
  if bdec (ltb k e)
  then let u = get xsrc k in
       cnt_loop xsrc e (add k (Uint63.of_int (1)))
         (set c u (add (get c u) (Uint63.of_int (1))))
  else c

(** val pre_loop :
    Uint63.t -> Uint63.t -> Uint63.t Marray.t -> Uint63.t Marray.t **)

let rec pre_loop v i c =
  if bdec (ltb i v)
  then pre_loop v (add i (Uint63.of_int (1)))
         (set c (add i (Uint63.of_int (1)))
           (add (get c (add i (Uint63.of_int (1)))) (get c i)))
  else c

(** val rfill_loop :
    Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t Marray.t
    -> Uint63.t Marray.t -> Uint63.t Marray.t * Uint63.t Marray.t **)

let rec rfill_loop xsrc xdst k c adj =
  if bdec (ltb (Uint63.of_int (0)) k)
  then let k1 = sub k (Uint63.of_int (1)) in
       let u = get xsrc k1 in
       let p = sub (get c u) (Uint63.of_int (1)) in
       rfill_loop xsrc xdst k1 (set c u p) (set adj p (get xdst k1))
  else (c, adj)

(** val ind_loop :
    Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t Marray.t ->
    Uint63.t Marray.t **)

let rec ind_loop adj e j d =
  if bdec (ltb j e)
  then let v = get adj j in
       ind_loop adj e (add j (Uint63.of_int (1)))
         (set d v (add (get d v) (Uint63.of_int (1))))
  else d

(** val q0_loop :
    Uint63.t -> Uint63.t -> Uint63.t Marray.t -> Uint63.t Marray.t ->
    Uint63.t -> Uint63.t Marray.t * Uint63.t **)

let rec q0_loop v x d q t =
  if bdec (ltb x v)
  then if eqb (get d x) (Uint63.of_int (0))
       then q0_loop v (add x (Uint63.of_int (1))) d (set q t x)
              (add t (Uint63.of_int (1)))
       else q0_loop v (add x (Uint63.of_int (1))) d q t
  else (q, t)

(** val relax1 :
    string -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t Marray.t ->
    Uint63.t Marray.t **)

let relax1 xs v du v0 dist =
  if eqb du nEG
  then dist
  else let cand = add du (wt xs v v0) in
       if ltsb (get dist v0) cand then set dist v0 cand else dist

(** val relax_loop :
    string -> Uint63.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t ->
    Uint63.t -> Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t Marray.t
    -> Uint63.t -> ((Uint63.t Marray.t * Uint63.t Marray.t) * Uint63.t
    Marray.t) * Uint63.t **)

let rec relax_loop xs v adj du hi j d dist q t =
  if bdec (ltb j hi)
  then let v0 = get adj j in
       let dist' = relax1 xs v du v0 dist in
       let e = sub (get d v0) (Uint63.of_int (1)) in
       if eqb e (Uint63.of_int (0))
       then relax_loop xs v adj du hi (add j (Uint63.of_int (1)))
              (set d v0 e) dist' (set q t v0) (add t (Uint63.of_int (1)))
       else relax_loop xs v adj du hi (add j (Uint63.of_int (1)))
              (set d v0 e) dist' q t
  else (((d, dist), q), t)

(** val kahn_loop :
    string -> Uint63.t -> Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t
    -> Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t Marray.t ->
    Uint63.t -> Uint63.t Marray.t **)

let rec kahn_loop xs v off adj h d dist q t =
  if bdec (ltb h t)
  then let u = get q h in
       let lo = get off u in
       let (p, t') =
         relax_loop xs v adj (get dist u)
           (get off (add u (Uint63.of_int (1)))) lo d dist q t
       in
       let (p0, q') = p in
       let (d', dist') = p0 in
       kahn_loop xs v off adj (add h (Uint63.of_int (1))) d' dist' q' t'
  else dist

(** val excavator_impl :
    string -> Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t **)

let excavator_impl xs xsrc xdst =
  let v = length0 xs in
  let e = length xsrc in
  let c =
    cnt_loop xsrc e (Uint63.of_int (0))
      (make (add v (Uint63.of_int (1))) (Uint63.of_int (0)))
  in
  let c0 = pre_loop v (Uint63.of_int (0)) c in
  let (off, adj) = rfill_loop xsrc xdst e c0 (make e (Uint63.of_int (0))) in
  let d = ind_loop adj e (Uint63.of_int (0)) (make v (Uint63.of_int (0))) in
  let (q, t) =
    q0_loop v (Uint63.of_int (0)) d (make v (Uint63.of_int (0)))
      (Uint63.of_int (0))
  in
  let dist = set (make v nEG) (Uint63.of_int (0)) (Uint63.of_int (0)) in
  let dist0 = kahn_loop xs v off adj (Uint63.of_int (0)) d dist q t in
  get dist0 (sub v (Uint63.of_int (1)))

module ExcavatorexpeditionImpl =
 struct
  (** val excavator : string -> uint Marray.t -> uint Marray.t -> sint **)

  let excavator =
    excavator_impl
 end
