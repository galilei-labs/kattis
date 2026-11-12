
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

(** val bdec : bool -> bool **)

let bdec = function
| true -> true
| false -> false

type trie = { tchr : Uint63.t Marray.t; tpar : Uint63.t Marray.t;
              tfc : Uint63.t Marray.t; tns : Uint63.t Marray.t;
              tdep : Uint63.t Marray.t; tn : Uint63.t }

(** val lookup_from :
    Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t **)

let rec lookup_from chr ns c v =
  if bdec (eqb v (Uint63.of_int (0)))
  then (Uint63.of_int (0))
  else if eqb (get chr v) c
       then v
       else let nx = get ns v in
            if bdec (ltb nx v)
            then lookup_from chr ns c nx
            else (Uint63.of_int (0))

(** val lookup : trie -> Uint63.t -> Uint63.t -> Uint63.t **)

let lookup t u c =
  let v = get t.tfc u in lookup_from t.tchr t.tns c v

(** val add_child : trie -> Uint63.t -> Uint63.t -> trie * Uint63.t **)

let add_child t u c =
  let v = lookup t u c in
  if eqb v (Uint63.of_int (0))
  then let n = t.tn in
       let old = get t.tfc u in
       let du = get t.tdep u in
       ({ tchr = (set t.tchr n c); tpar = (set t.tpar n u); tfc =
       (set t.tfc u n); tns = (set t.tns n old); tdep =
       (set t.tdep n (add du (Uint63.of_int (1)))); tn =
       (add n (Uint63.of_int (1))) }, n)
  else (t, v)

type bstate = { bact : Uint63.t Marray.t; bcur : Uint63.t Marray.t;
                bw : Uint63.t; bt : trie }

(** val round_loop :
    string Marray.t -> Uint63.t -> Uint63.t -> Uint63.t -> bstate -> bstate **)

let rec round_loop pats d na k st =
  if bdec (ltb k na)
  then let act = st.bact in
       let i = get act k in
       let s = get pats i in
       let cur = st.bcur in
       let tv = add_child st.bt (get cur i) (get0 s d) in
       let cur' = set cur i (snd tv) in
       let w = st.bw in
       if ltb (add d (Uint63.of_int (1))) (length0 s)
       then round_loop pats d na (add k (Uint63.of_int (1))) { bact =
              (set act w i); bcur = cur'; bw = (add w (Uint63.of_int (1)));
              bt = (fst tv) }
       else round_loop pats d na (add k (Uint63.of_int (1))) { bact = act;
              bcur = cur'; bw = w; bt = (fst tv) }
  else st

(** val rounds :
    string Marray.t -> Uint63.t -> Uint63.t -> bstate -> bstate **)

let rec rounds pats l d st =
  if bdec (ltb d l)
  then let st' =
         round_loop pats d st.bw (Uint63.of_int (0)) { bact = st.bact; bcur =
           st.bcur; bw = (Uint63.of_int (0)); bt = st.bt }
       in
       rounds pats l (add d (Uint63.of_int (1))) st'
  else st

(** val sums :
    string Marray.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t ->
    Uint63.t * Uint63.t **)

let rec sums pats m i p l =
  if bdec (ltb i m)
  then let l0 = length0 (get pats i) in
       sums pats m (add i (Uint63.of_int (1))) (add p l0)
         (if ltb l l0 then l0 else l)
  else (p, l)

(** val iota :
    Uint63.t -> Uint63.t -> Uint63.t Marray.t -> Uint63.t Marray.t **)

let rec iota m i a =
  if bdec (ltb i m) then iota m (add i (Uint63.of_int (1))) (set a i i) else a

(** val plist_loop :
    Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t Marray.t ->
    Uint63.t Marray.t -> Uint63.t Marray.t * Uint63.t Marray.t **)

let rec plist_loop cur m i fp np =
  if bdec (ltb i m)
  then let v = get cur i in
       let old = get fp v in
       plist_loop cur m (add i (Uint63.of_int (1)))
         (set fp v (add i (Uint63.of_int (1))))
         (set np (add i (Uint63.of_int (1))) old)
  else (fp, np)

(** val walk :
    trie -> Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t **)

let rec walk t fl c x =
  let y = lookup t x c in
  if bdec (eqb y (Uint63.of_int (0)))
  then if bdec (eqb x (Uint63.of_int (0)))
       then (Uint63.of_int (0))
       else let x' = get fl x in
            if bdec (ltb x' x) then walk t fl c x' else (Uint63.of_int (0))
  else y

(** val fail_loop :
    trie -> Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t Marray.t ->
    Uint63.t Marray.t -> Uint63.t Marray.t * Uint63.t Marray.t **)

let rec fail_loop t fp n v fl out =
  if bdec (ltb v n)
  then let u = get t.tpar v in
       let c = get t.tchr v in
       let f =
         if eqb u (Uint63.of_int (0))
         then (Uint63.of_int (0))
         else let x = get fl u in walk t fl c x
       in
       let o = if eqb (get fp f) (Uint63.of_int (0)) then get out f else f in
       fail_loop t fp n (add v (Uint63.of_int (1))) (set fl v f) (set out v o)
  else (fl, out)

(** val emit_list :
    ('a1 -> Uint63.t -> Uint63.t -> 'a1) -> Uint63.t Marray.t -> Uint63.t ->
    Uint63.t -> 'a1 -> 'a1 **)

let rec emit_list f np p e s =
  if bdec (eqb e (Uint63.of_int (0)))
  then s
  else let s' = f s (sub e (Uint63.of_int (1))) p in
       let e' = get np e in
       if bdec (ltb e' e) then emit_list f np p e' s' else s'

(** val emit_chain :
    ('a1 -> Uint63.t -> Uint63.t -> 'a1) -> trie -> Uint63.t Marray.t ->
    Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t -> 'a1 ->
    'a1 **)

let rec emit_chain f t out fp np je x s =
  if bdec (eqb x (Uint63.of_int (0)))
  then s
  else let e = get fp x in
       let s' = emit_list f np (sub je (get t.tdep x)) e s in
       let o = get out x in
       if bdec (ltb o x) then emit_chain f t out fp np je o s' else s'

(** val scan :
    ('a1 -> Uint63.t -> Uint63.t -> 'a1) -> trie -> Uint63.t Marray.t ->
    Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t Marray.t -> string ->
    Uint63.t -> Uint63.t -> Uint63.t -> 'a1 -> 'a1 **)

let rec scan f t fl out fp np txt n j st s =
  if bdec (ltb j n)
  then let st' = walk t fl (get0 txt j) st in
       let s' = emit_chain f t out fp np (add j (Uint63.of_int (1))) st' s in
       scan f t fl out fp np txt n (add j (Uint63.of_int (1))) st' s'
  else s

(** val f_cnt :
    Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t Marray.t **)

let f_cnt cnt i _ =
  let c = get cnt i in set cnt i (add c (Uint63.of_int (1)))

(** val f_fill :
    (Uint63.t Marray.t Marray.t * Uint63.t Marray.t) -> Uint63.t -> Uint63.t
    -> Uint63.t Marray.t Marray.t * Uint63.t Marray.t **)

let f_fill st i p =
  let rows = fst st in
  let ptr = snd st in
  let k = get ptr i in
  let row = get rows i in
  ((set rows i (set row k p)), (set ptr i (add k (Uint63.of_int (1)))))

(** val alloc_loop :
    Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t Marray.t Marray.t
    -> Uint63.t Marray.t Marray.t **)

let rec alloc_loop cnt m i rows =
  if bdec (ltb i m)
  then alloc_loop cnt m (add i (Uint63.of_int (1)))
         (set rows i (make (get cnt i) (Uint63.of_int (0))))
  else rows

(** val multimatch_impl :
    string Marray.t -> string -> uint Marray.t Marray.t **)

let multimatch_impl pats txt =
  let m = length pats in
  let pL =
    sums pats m (Uint63.of_int (0)) (Uint63.of_int (0)) (Uint63.of_int (0))
  in
  let cap = add (fst pL) (Uint63.of_int (1)) in
  let l = snd pL in
  let t0 = { tchr = (make cap (Uint63.of_int (0))); tpar =
    (make cap (Uint63.of_int (0))); tfc = (make cap (Uint63.of_int (0)));
    tns = (make cap (Uint63.of_int (0))); tdep =
    (make cap (Uint63.of_int (0))); tn = (Uint63.of_int (1)) }
  in
  let act0 = iota m (Uint63.of_int (0)) (make m (Uint63.of_int (0))) in
  let st =
    rounds pats l (Uint63.of_int (0)) { bact = act0; bcur =
      (make m (Uint63.of_int (0))); bw = m; bt = t0 }
  in
  let t = st.bt in
  let pl =
    plist_loop st.bcur m (Uint63.of_int (0)) (make cap (Uint63.of_int (0)))
      (make (add m (Uint63.of_int (1))) (Uint63.of_int (0)))
  in
  let fp = fst pl in
  let np = snd pl in
  let fo =
    fail_loop t fp t.tn (Uint63.of_int (1)) (make cap (Uint63.of_int (0)))
      (make cap (Uint63.of_int (0)))
  in
  let fl = fst fo in
  let out = snd fo in
  let n = length0 txt in
  let cnt =
    scan f_cnt t fl out fp np txt n (Uint63.of_int (0)) (Uint63.of_int (0))
      (make m (Uint63.of_int (0)))
  in
  let rows =
    alloc_loop cnt m (Uint63.of_int (0))
      (make m (make (Uint63.of_int (0)) (Uint63.of_int (0))))
  in
  fst
    (scan f_fill t fl out fp np txt n (Uint63.of_int (0)) (Uint63.of_int (0))
      (rows, (make m (Uint63.of_int (0)))))

(** val multimatch : string Marray.t -> string -> uint Marray.t Marray.t **)

let multimatch =
  multimatch_impl
