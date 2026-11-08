
(** val add : Uint63.t -> Uint63.t -> Uint63.t **)

let add = Uint63.add

(** val sub : Uint63.t -> Uint63.t -> Uint63.t **)

let sub = Uint63.sub

(** val eqb : Uint63.t -> Uint63.t -> bool **)

let eqb = Uint63.equal

(** val ltb : Uint63.t -> Uint63.t -> bool **)

let ltb = Uint63.lt

type char63 = Uint63.t

type string = Pstring.t

(** val length : string -> Uint63.t **)

let length = Pstring.length

(** val get : string -> Uint63.t -> char63 **)

let get = Pstring.get

type uint = Uint63.t

(** val bdec : bool -> bool **)

let bdec = function
| true -> true
| false -> false

(** val scan :
    string -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t ->
    Uint63.t -> Uint63.t -> Uint63.t * Uint63.t **)

let rec scan x n k p mx imx mn imn =
  if bdec (ltb k n)
  then let p' =
         if eqb (get x k) (Uint63.of_int (82))
         then add p (Uint63.of_int (1))
         else sub p (Uint63.of_int (1))
       in
       let k' = add k (Uint63.of_int (1)) in
       if ltb mx p'
       then scan x n k' p' p' k' mn imn
       else if ltb p' mn
            then scan x n k' p' mx imx p' k'
            else scan x n k' p' mx imx mn imn
  else (imx, imn)

(** val purplerain_impl : string -> uint * uint **)

let purplerain_impl x =
  let n = length x in
  let (a, b) =
    scan x n (Uint63.of_int (0)) n n (Uint63.of_int (0)) n (Uint63.of_int (0))
  in
  if ltb a b
  then ((add a (Uint63.of_int (1))), b)
  else ((add b (Uint63.of_int (1))), a)

(** val purplerain : string -> uint * uint **)

let purplerain =
  purplerain_impl
