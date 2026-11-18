
(** val fst : ('a1 * 'a2) -> 'a1 **)

let fst = function
| (x, _) -> x

(** val snd : ('a1 * 'a2) -> 'a2 **)

let snd = function
| (_, y) -> y

(** val add : Uint63.t -> Uint63.t -> Uint63.t **)

let add = Uint63.add

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

(** val bdec : bool -> bool **)

let bdec = function
| true -> true
| false -> false

(** val find :
    Uint63.t Marray.t -> Uint63.t -> Uint63.t * Uint63.t Marray.t **)

let rec find par x =
  let p = get par x in
  if bdec (eqb p x)
  then (x, par)
  else let rp = find par p in ((fst rp), (set (snd rp) x (fst rp)))

(** val link :
    Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t ->
    Uint63.t Marray.t * Uint63.t Marray.t **)

let link par rk ra rb =
  if eqb ra rb
  then (par, rk)
  else let ka = get rk ra in
       let kb = get rk rb in
       if ltb ka kb
       then ((set par ra rb), rk)
       else if ltb kb ka
            then ((set par rb ra), rk)
            else ((set par ra rb), (set rk rb (add kb (Uint63.of_int (1)))))

(** val init_loop :
    Uint63.t -> Uint63.t -> Uint63.t Marray.t -> Uint63.t Marray.t **)

let rec init_loop n i p =
  if bdec (ltb i n)
  then init_loop n (add i (Uint63.of_int (1))) (set p i i)
  else p

(** val init_par : Uint63.t -> Uint63.t Marray.t **)

let init_par n =
  init_loop n (Uint63.of_int (0)) (make n (Uint63.of_int (0)))

(** val scan :
    bool Marray.t -> Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t ->
    Uint63.t -> Uint63.t Marray.t -> Uint63.t Marray.t -> bool Marray.t ->
    bool Marray.t **)

let rec scan xu xa xb q k par rk out =
  if bdec (ltb k q)
  then let a = get xa k in
       let b = get xb k in
       let fa = find par a in
       let fb = find (snd fa) b in
       if get xu k
       then let l = link (snd fb) rk (fst fa) (fst fb) in
            scan xu xa xb q (add k (Uint63.of_int (1))) (fst l) (snd l) out
       else scan xu xa xb q (add k (Uint63.of_int (1))) (snd fb) rk
              (set out k (eqb (fst fa) (fst fb)))
  else out

(** val run_ops_raw :
    uint -> bool Marray.t -> uint Marray.t -> uint Marray.t -> bool Marray.t **)

let run_ops_raw xn xu xa xb =
  let q = length xu in
  scan xu xa xb q (Uint63.of_int (0)) (init_par xn)
    (make xn (Uint63.of_int (0))) (make q false)

(** val count_queries :
    bool Marray.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t **)

let rec count_queries xu q k c =
  if bdec (ltb k q)
  then count_queries xu q (add k (Uint63.of_int (1)))
         (if get xu k then c else add c (Uint63.of_int (1)))
  else c

(** val pack_queries :
    bool Marray.t -> bool Marray.t -> Uint63.t -> Uint63.t -> Uint63.t ->
    bool Marray.t -> bool Marray.t **)

let rec pack_queries xu raw q k c out =
  if bdec (ltb k q)
  then if get xu k
       then pack_queries xu raw q (add k (Uint63.of_int (1))) c out
       else pack_queries xu raw q (add k (Uint63.of_int (1)))
              (add c (Uint63.of_int (1))) (set out c (get raw k))
  else out

(** val compact_queries : bool Marray.t -> bool Marray.t -> bool Marray.t **)

let compact_queries xu raw =
  let q = length xu in
  let count = count_queries xu q (Uint63.of_int (0)) (Uint63.of_int (0)) in
  pack_queries xu raw q (Uint63.of_int (0)) (Uint63.of_int (0))
    (make count false)

(** val run_ops_impl :
    uint -> bool Marray.t -> uint Marray.t -> uint Marray.t -> bool Marray.t **)

let run_ops_impl xn xu xa xb =
  compact_queries xu (run_ops_raw xn xu xa xb)

(** val run_ops :
    uint -> bool Marray.t -> uint Marray.t -> uint Marray.t -> bool Marray.t **)

let run_ops =
  run_ops_impl
