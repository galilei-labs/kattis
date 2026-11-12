
(** val add : Uint63.t -> Uint63.t -> Uint63.t **)

let add = Uint63.add

(** val sub : Uint63.t -> Uint63.t -> Uint63.t **)

let sub = Uint63.sub

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

type uint = Uint63.t

(** val bdec : bool -> bool **)

let bdec = function
| true -> true
| false -> false

(** val minloop :
    Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t ->
    Uint63.t -> Uint63.t -> Uint63.t **)

let rec minloop c t x hi j acc =
  if bdec (ltb j hi)
  then let v = get t (sub x (get c j)) in
       minloop c t x hi (add j (Uint63.of_int (1)))
         (if ltb v acc then v else acc)
  else acc

(** val kupd :
    Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t **)

let kupd c n x k =
  if ltb (add k (Uint63.of_int (1))) n
  then if leb (get c (add k (Uint63.of_int (1)))) x
       then add k (Uint63.of_int (1))
       else k
  else k

(** val outer :
    Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t ->
    Uint63.t Marray.t -> Uint63.t Marray.t -> bool **)

let rec outer c n b x k t g =
  if bdec (ltb x b)
  then let k' = kupd c n x k in
       let gx = add (get g (sub x (get c k'))) (Uint63.of_int (1)) in
       let tx =
         add
           (minloop c t x (add k' (Uint63.of_int (1))) (Uint63.of_int (1))
             (get t (sub x (Uint63.of_int (1)))))
           (Uint63.of_int (1))
       in
       if ltb tx gx
       then false
       else outer c n b (add x (Uint63.of_int (1))) k' (set t x tx)
              (set g x gx)
  else true

(** val bound : Uint63.t Marray.t -> Uint63.t **)

let bound c =
  let n = length c in
  add (get c (sub n (Uint63.of_int (1)))) (get c (sub n (Uint63.of_int (2))))

(** val run : Uint63.t Marray.t -> bool **)

let run c =
  let b = bound c in
  outer c (length c) b (Uint63.of_int (1)) (Uint63.of_int (0))
    (make b (Uint63.of_int (0))) (make b (Uint63.of_int (0)))

(** val canonical_impl : uint Marray.t -> bool **)

let canonical_impl =
  run

(** val canonical : uint Marray.t -> bool **)

let canonical =
  canonical_impl
