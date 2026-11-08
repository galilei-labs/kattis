
(** val add : Uint63.t -> Uint63.t -> Uint63.t **)

let add = Uint63.add

(** val sub : Uint63.t -> Uint63.t -> Uint63.t **)

let sub = Uint63.sub

(** val mul : Uint63.t -> Uint63.t -> Uint63.t **)

let mul = Uint63.mul

(** val div : Uint63.t -> Uint63.t -> Uint63.t **)

let div = Uint63.div

(** val mod0 : Uint63.t -> Uint63.t -> Uint63.t **)

let mod0 = Uint63.rem

(** val eqb : Uint63.t -> Uint63.t -> bool **)

let eqb = Uint63.equal

(** val ltb : Uint63.t -> Uint63.t -> bool **)

let ltb = Uint63.lt

(** val leb : Uint63.t -> Uint63.t -> bool **)

let leb = Uint63.le

type uint = Uint63.t

(** val bdec : bool -> bool **)

let bdec = function
| true -> true
| false -> false

(** val divout : Uint63.t -> Uint63.t -> Uint63.t **)

let rec divout p m =
  if bdec
       ((&&) (eqb (mod0 m p) (Uint63.of_int (0)))
         ((&&) (ltb (Uint63.of_int (0)) m) (ltb (Uint63.of_int (1)) p)))
  then divout p (div m p)
  else m

(** val outer : Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t **)

let rec outer p m res =
  if bdec ((&&) (leb (mul p p) m) (ltb p m))
  then if eqb (mod0 m p) (Uint63.of_int (0))
       then let m' = divout p m in
            outer (add p (Uint63.of_int (1))) m'
              (mul (div res p) (sub p (Uint63.of_int (1))))
       else outer (add p (Uint63.of_int (1))) m res
  else if ltb (Uint63.of_int (1)) m
       then mul (div res m) (sub m (Uint63.of_int (1)))
       else res

(** val relatives_impl : uint -> uint **)

let relatives_impl n =
  if leb n (Uint63.of_int (1))
  then (Uint63.of_int (0))
  else outer (Uint63.of_int (2)) n n

(** val relatives : uint -> uint **)

let relatives =
  relatives_impl
