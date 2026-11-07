
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

(** val sd_loop : Uint63.t -> Uint63.t -> Uint63.t **)

let rec sd_loop n p =
  if bdec ((&&) (ltb p n) (leb (mul p p) n))
  then if eqb (mod0 n p) (Uint63.of_int (0))
       then p
       else sd_loop n (add p (Uint63.of_int (1)))
  else n

(** val pascal_impl : uint -> uint **)

let pascal_impl n =
  sub n (div n (sd_loop n (Uint63.of_int (2))))

module PascalImpl =
 struct
  (** val pascal : uint -> uint **)

  let pascal =
    pascal_impl
 end
