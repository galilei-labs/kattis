
(** val fst : ('a1 * 'a2) -> 'a1 **)

let fst = function
| (x, _) -> x

(** val snd : ('a1 * 'a2) -> 'a2 **)

let snd = function
| (_, y) -> y

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

(** val init_rank :
    string -> Uint63.t -> Uint63.t -> Uint63.t array -> Uint63.t array **)

let rec init_rank x n i r =
  if bdec (ltb i n)
  then init_rank x n (add i (Uint63.of_int (1)))
         ((fun a i v -> Array.unsafe_set a (Uint63.hash i) v; a) r i
           (add (get x i) (Uint63.of_int (1))))
  else r

(** val init_id : Uint63.t -> Uint63.t -> Uint63.t array -> Uint63.t array **)

let rec init_id n i sa =
  if bdec (ltb i n)
  then init_id n (add i (Uint63.of_int (1)))
         ((fun a i v -> Array.unsafe_set a (Uint63.hash i) v; a) sa i i)
  else sa

(** val skey :
    Uint63.t array -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t **)

let skey r n k x =
  if ltb (add x k) n
  then (fun a i -> Array.unsafe_get a (Uint63.hash i)) r (add x k)
  else (Uint63.of_int (0))

(** val cbound : Uint63.t -> Uint63.t **)

let cbound n =
  if ltb n (Uint63.of_int (256))
  then (Uint63.of_int (257))
  else add n (Uint63.of_int (1))

(** val count_loop :
    Uint63.t array -> Uint63.t -> Uint63.t -> Uint63.t array -> Uint63.t ->
    Uint63.t array -> Uint63.t array **)

let rec count_loop r n k src i cnt =
  if bdec (ltb i n)
  then let x = (fun a i -> Array.unsafe_get a (Uint63.hash i)) src i in
       let v =
         if ltb (add x k) n
         then (fun a i -> Array.unsafe_get a (Uint63.hash i)) r (add x k)
         else (Uint63.of_int (0))
       in
       count_loop r n k src (add i (Uint63.of_int (1)))
         ((fun a i v -> Array.unsafe_set a (Uint63.hash i) v; a) cnt v
           (add ((fun a i -> Array.unsafe_get a (Uint63.hash i)) cnt v)
             (Uint63.of_int (1))))
  else cnt

(** val prefix_loop :
    Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t array -> Uint63.t array **)

let rec prefix_loop b v acc cnt =
  if bdec (ltb v b)
  then let c = (fun a i -> Array.unsafe_get a (Uint63.hash i)) cnt v in
       prefix_loop b (add v (Uint63.of_int (1))) (add acc c)
         ((fun a i v -> Array.unsafe_set a (Uint63.hash i) v; a) cnt v acc)
  else cnt

(** val place_loop :
    Uint63.t array -> Uint63.t -> Uint63.t -> Uint63.t array -> Uint63.t ->
    Uint63.t array -> Uint63.t array -> Uint63.t array **)

let rec place_loop r n k src i cnt dst =
  if bdec (ltb i n)
  then let x = (fun a i -> Array.unsafe_get a (Uint63.hash i)) src i in
       let v =
         if ltb (add x k) n
         then (fun a i -> Array.unsafe_get a (Uint63.hash i)) r (add x k)
         else (Uint63.of_int (0))
       in
       let p = (fun a i -> Array.unsafe_get a (Uint63.hash i)) cnt v in
       place_loop r n k src (add i (Uint63.of_int (1)))
         ((fun a i v -> Array.unsafe_set a (Uint63.hash i) v; a) cnt v
           (add p (Uint63.of_int (1))))
         ((fun a i v -> Array.unsafe_set a (Uint63.hash i) v; a) dst p x)
  else dst

(** val csort :
    Uint63.t array -> Uint63.t -> Uint63.t -> Uint63.t array -> Uint63.t
    array -> Uint63.t array **)

let csort r n k src dst =
  let b = cbound n in
  let c0 =
    count_loop r n k src (Uint63.of_int (0))
      ((fun n d -> Array.make (Uint63.hash n) d) b (Uint63.of_int (0)))
  in
  let c1 = prefix_loop b (Uint63.of_int (0)) (Uint63.of_int (0)) c0 in
  place_loop r n k src (Uint63.of_int (0)) c1 dst

(** val rank_loop :
    Uint63.t array -> Uint63.t -> Uint63.t -> Uint63.t array -> Uint63.t ->
    Uint63.t -> Uint63.t array -> Uint63.t array * Uint63.t **)

let rec rank_loop r n k sa t cur nr =
  if bdec (ltb t n)
  then let a =
         (fun a i -> Array.unsafe_get a (Uint63.hash i)) sa
           (sub t (Uint63.of_int (1)))
       in
       let b = (fun a i -> Array.unsafe_get a (Uint63.hash i)) sa t in
       let c =
         if if eqb ((fun a i -> Array.unsafe_get a (Uint63.hash i)) r a)
                 ((fun a i -> Array.unsafe_get a (Uint63.hash i)) r b)
            then eqb (skey r n k a) (skey r n k b)
            else false
         then cur
         else add cur (Uint63.of_int (1))
       in
       rank_loop r n k sa (add t (Uint63.of_int (1))) c
         ((fun a i v -> Array.unsafe_set a (Uint63.hash i) v; a) nr b c)
  else (nr, cur)

(** val rounds :
    Uint63.t -> Uint63.t -> Uint63.t array -> Uint63.t array -> Uint63.t
    array -> Uint63.t array -> Uint63.t array **)

let rec rounds n k r nr sa tmp =
  let tmp1 = csort r n k sa tmp in
  let sa1 = csort r n (Uint63.of_int (0)) tmp1 sa in
  let q =
    rank_loop r n k sa1 (Uint63.of_int (1)) (Uint63.of_int (1))
      ((fun a i v -> Array.unsafe_set a (Uint63.hash i) v; a) nr
        ((fun a i -> Array.unsafe_get a (Uint63.hash i)) sa1
          (Uint63.of_int (0)))
        (Uint63.of_int (1)))
  in
  if eqb (snd q) n
  then sa1
  else if bdec ((&&) (ltb k (add k k)) (ltb (add k k) n))
       then rounds n (add k k) (fst q) r sa1 tmp1
       else sa1

(** val suffix_array_impl : string -> uint array **)

let suffix_array_impl x =
  let n = length x in
  let r =
    init_rank x n (Uint63.of_int (0))
      ((fun n d -> Array.make (Uint63.hash n) d) n (Uint63.of_int (0)))
  in
  let sa =
    init_id n (Uint63.of_int (0))
      ((fun n d -> Array.make (Uint63.hash n) d) n (Uint63.of_int (0)))
  in
  rounds n (Uint63.of_int (1)) r
    ((fun n d -> Array.make (Uint63.hash n) d) n (Uint63.of_int (0))) sa
    ((fun n d -> Array.make (Uint63.hash n) d) n (Uint63.of_int (0)))

(** val suffix_array : string -> uint array **)

let suffix_array =
  suffix_array_impl
