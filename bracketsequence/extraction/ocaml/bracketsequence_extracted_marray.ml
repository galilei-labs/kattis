
(** val negb : bool -> bool **)

let negb = function
| true -> false
| false -> true

(** val add : Uint63.t -> Uint63.t -> Uint63.t **)

let add = Uint63.add

(** val sub : Uint63.t -> Uint63.t -> Uint63.t **)

let sub = Uint63.sub

(** val mul : Uint63.t -> Uint63.t -> Uint63.t **)

let mul = Uint63.mul

(** val mod0 : Uint63.t -> Uint63.t -> Uint63.t **)

let mod0 = Uint63.rem

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

type 'a token =
| Open
| Close
| Num of 'a

(** val bdec : bool -> bool **)

let bdec = function
| true -> true
| false -> false

(** val mi : Uint63.t **)

let mi =
  (Uint63.of_int (1000000007))

(** val opm : bool -> Uint63.t -> Uint63.t -> Uint63.t **)

let opm add0 a v =
  if add0 then mod0 (add a v) mi else mod0 (mul a v) mi

(** val idm : bool -> Uint63.t **)

let idm = function
| true -> (Uint63.of_int (0))
| false -> (Uint63.of_int (1))

(** val loop :
    uint token Marray.t -> Uint63.t -> Uint63.t -> Uint63.t -> bool ->
    Uint63.t Marray.t -> Uint63.t **)

let rec loop x n i d add0 stk =
  if bdec (ltb i n)
  then (match get x i with
        | Open ->
          loop x n (add i (Uint63.of_int (1))) (add d (Uint63.of_int (1)))
            (negb add0)
            (set stk (add d (Uint63.of_int (1))) (idm (negb add0)))
        | Close ->
          if eqb d (Uint63.of_int (0))
          then loop x n (add i (Uint63.of_int (1))) d add0 stk
          else loop x n (add i (Uint63.of_int (1)))
                 (sub d (Uint63.of_int (1))) (negb add0)
                 (set stk (sub d (Uint63.of_int (1)))
                   (opm (negb add0) (get stk (sub d (Uint63.of_int (1))))
                     (get stk d)))
        | Num v ->
          loop x n (add i (Uint63.of_int (1))) d add0
            (set stk d (opm add0 (get stk d) v)))
  else get stk d

(** val bracketsequence_impl : uint token Marray.t -> uint **)

let bracketsequence_impl x =
  let n = length x in
  loop x n (Uint63.of_int (0)) (Uint63.of_int (0)) true
    (make (add n (Uint63.of_int (1))) (Uint63.of_int (0)))

(** val bracketsequence : uint token Marray.t -> uint **)

let bracketsequence =
  bracketsequence_impl
