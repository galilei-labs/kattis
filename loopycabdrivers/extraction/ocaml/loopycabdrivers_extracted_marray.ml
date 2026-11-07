
(** val fst : ('a1 * 'a2) -> 'a1 **)

let fst = function
| (x, _) -> x

(** val snd : ('a1 * 'a2) -> 'a2 **)

let snd = function
| (_, y) -> y

type comparison =
| Eq
| Lt
| Gt

(** val land0 : Uint63.t -> Uint63.t -> Uint63.t **)

let land0 = Uint63.l_and

(** val add : Uint63.t -> Uint63.t -> Uint63.t **)

let add = Uint63.add

(** val sub : Uint63.t -> Uint63.t -> Uint63.t **)

let sub = Uint63.sub

(** val mul : Uint63.t -> Uint63.t -> Uint63.t **)

let mul = Uint63.mul

(** val div : Uint63.t -> Uint63.t -> Uint63.t **)

let div = Uint63.div

(** val eqb : Uint63.t -> Uint63.t -> bool **)

let eqb = Uint63.equal

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

(** val copy : 'a1 Marray.t -> 'a1 Marray.t **)

let copy = Marray.copy

type char63 = Uint63.t

type string = Pstring.t

(** val make0 : Uint63.t -> char63 -> string **)

let make0 = Pstring.make

(** val length0 : string -> Uint63.t **)

let length0 = Pstring.length

(** val get0 : string -> Uint63.t -> char63 **)

let get0 = Pstring.get

(** val compare : string -> string -> comparison **)

let compare = (fun x y -> let c = Pstring.compare x y in if c = 0 then Eq else if c < 0 then Lt else Gt)

(** val bdec : bool -> bool **)

let bdec = function
| true -> true
| false -> false

(** val hloop : string -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t **)

let rec hloop s n k h =
  if bdec (ltb k n)
  then hloop s n (add k (Uint63.of_int (1)))
         (add (mul h (Uint63.of_int (31))) (get0 s k))
  else h

(** val hmask : Uint63.t **)

let hmask =
  (Uint63.of_int (65535))

(** val hsize : Uint63.t **)

let hsize =
  (Uint63.of_int (65536))

(** val hash : string -> Uint63.t **)

let hash s =
  land0 (hloop s (length0 s) (Uint63.of_int (0)) (Uint63.of_int (7))) hmask

(** val probe :
    Uint63.t Marray.t -> string Marray.t -> string -> Uint63.t -> Uint63.t ->
    Uint63.t * bool **)

let rec probe tbl names s t p =
  if bdec (ltb p t)
  then let e = get tbl p in
       if eqb e (Uint63.of_int (0))
       then (p, false)
       else (match compare (get names (sub e (Uint63.of_int (1)))) s with
             | Eq -> (p, true)
             | _ -> probe tbl names s t (add p (Uint63.of_int (1))))
  else (p, false)

type hstate = { ht : Uint63.t Marray.t; hn : string Marray.t; hc : Uint63.t }

(** val lookup : hstate -> string -> hstate * Uint63.t **)

let lookup st s =
  let tbl = st.ht in
  let t = length tbl in
  let pf = probe tbl st.hn s t (hash s) in
  let p = fst pf in
  if snd pf
  then (st, (sub (get tbl p) (Uint63.of_int (1))))
  else ({ ht = (set tbl p (add st.hc (Uint63.of_int (1)))); hn =
         (set st.hn st.hc s); hc = (add st.hc (Uint63.of_int (1))) }, st.hc)

(** val idloop :
    string Marray.t -> string Marray.t -> Uint63.t -> Uint63.t -> hstate ->
    Uint63.t Marray.t -> Uint63.t Marray.t -> (hstate * Uint63.t
    Marray.t) * Uint63.t Marray.t **)

let rec idloop x y m k st is id =
  if bdec (ltb k m)
  then let r1 = lookup st (get x k) in
       let r2 = lookup (fst r1) (get y k) in
       idloop x y m (add k (Uint63.of_int (1))) (fst r2) (set is k (snd r1))
         (set id k (snd r2))
  else ((st, is), id)

(** val cnt_loop :
    (Uint63.t -> Uint63.t) -> Uint63.t -> Uint63.t -> Uint63.t Marray.t ->
    Uint63.t Marray.t **)

let rec cnt_loop es m k cnt =
  if bdec (ltb k m)
  then let u = es k in
       cnt_loop es m (add k (Uint63.of_int (1)))
         (set cnt u (add (get cnt u) (Uint63.of_int (1))))
  else cnt

(** val pre_loop :
    Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t Marray.t ->
    Uint63.t Marray.t **)

let rec pre_loop cnt v u off =
  if bdec (ltb u v)
  then pre_loop cnt v (add u (Uint63.of_int (1)))
         (set off (add u (Uint63.of_int (1))) (add (get off u) (get cnt u)))
  else off

(** val fill_loop :
    (Uint63.t -> Uint63.t) -> (Uint63.t -> Uint63.t) -> Uint63.t -> Uint63.t
    -> Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t Marray.t **)

let rec fill_loop es ed m k pos adj =
  if bdec (ltb k m)
  then let u = es k in
       let p = get pos u in
       fill_loop es ed m (add k (Uint63.of_int (1)))
         (set pos u (add p (Uint63.of_int (1)))) (set adj p (ed k))
  else adj

(** val csr :
    Uint63.t -> Uint63.t -> (Uint63.t -> Uint63.t) -> (Uint63.t -> Uint63.t)
    -> Uint63.t Marray.t * Uint63.t Marray.t **)

let csr v m es ed =
  let cnt = cnt_loop es m (Uint63.of_int (0)) (make v (Uint63.of_int (0))) in
  let off =
    pre_loop cnt v (Uint63.of_int (0))
      (make (add v (Uint63.of_int (1))) (Uint63.of_int (0)))
  in
  let adj =
    fill_loop es ed m (Uint63.of_int (0)) (copy off)
      (make m (Uint63.of_int (0)))
  in
  (off, adj)

(** val scan :
    Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t **)

let rec scan mark adj e j =
  if bdec (ltb j e)
  then if eqb (get mark (get adj j)) (Uint63.of_int (0))
       then j
       else scan mark adj e (add j (Uint63.of_int (1)))
  else e

type d1 = { mk : Uint63.t Marray.t; sv : Uint63.t Marray.t;
            sc : Uint63.t Marray.t; po : Uint63.t Marray.t; sp : Uint63.t;
            np : Uint63.t; rt : Uint63.t }

(** val dfs_step :
    Uint63.t -> Uint63.t Marray.t -> Uint63.t Marray.t -> d1 -> d1 option **)

let dfs_step v off adj s =
  if ltb (Uint63.of_int (0)) s.sp
  then let t = sub s.sp (Uint63.of_int (1)) in
       let u = get s.sv t in
       let e = get off (add u (Uint63.of_int (1))) in
       let j = scan s.mk adj e (get s.sc t) in
       if ltb j e
       then let w = get adj j in
            Some { mk = (set s.mk w (Uint63.of_int (1))); sv =
            (set s.sv s.sp w); sc =
            (set (set s.sc t (add j (Uint63.of_int (1)))) s.sp (get off w));
            po = s.po; sp = (add s.sp (Uint63.of_int (1))); np = s.np; rt =
            s.rt }
       else Some { mk = s.mk; sv = s.sv; sc = s.sc; po = (set s.po s.np u);
              sp = t; np = (add s.np (Uint63.of_int (1))); rt = s.rt }
  else if ltb s.rt v
       then let r = s.rt in
            if eqb (get s.mk r) (Uint63.of_int (0))
            then Some { mk = (set s.mk r (Uint63.of_int (1))); sv =
                   (set s.sv (Uint63.of_int (0)) r); sc =
                   (set s.sc (Uint63.of_int (0)) (get off r)); po = s.po;
                   sp = (Uint63.of_int (1)); np = s.np; rt =
                   (add r (Uint63.of_int (1))) }
            else Some { mk = s.mk; sv = s.sv; sc = s.sc; po = s.po; sp =
                   s.sp; np = s.np; rt = (add r (Uint63.of_int (1))) }
       else None

(** val dfs :
    Uint63.t -> Uint63.t Marray.t -> Uint63.t Marray.t -> d1 -> Uint63.t ->
    Uint63.t -> Uint63.t Marray.t **)

let rec dfs v off adj s bound steps =
  if bdec (ltb steps bound)
  then (match dfs_step v off adj s with
        | Some s' -> dfs v off adj s' bound (add steps (Uint63.of_int (1)))
        | None -> s.po)
  else s.po

(** val push_preds :
    Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t
    Marray.t -> Uint63.t Marray.t -> Uint63.t -> (Uint63.t
    Marray.t * Uint63.t Marray.t) * Uint63.t **)

let rec push_preds radj c e j lab stk sp0 =
  if bdec (ltb j e)
  then let w = get radj j in
       if eqb (get lab w) (Uint63.of_int (0))
       then push_preds radj c e (add j (Uint63.of_int (1))) (set lab w c)
              (set stk sp0 w) (add sp0 (Uint63.of_int (1)))
       else push_preds radj c e (add j (Uint63.of_int (1))) lab stk sp0
  else ((lab, stk), sp0)

type d2 = { lb : Uint63.t Marray.t; sk : Uint63.t Marray.t; sq : Uint63.t;
            ii : Uint63.t; cc : Uint63.t }

(** val asg_step :
    Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t Marray.t -> d2 -> d2
    option **)

let asg_step roff radj post s =
  if ltb (Uint63.of_int (0)) s.sq
  then let t = sub s.sq (Uint63.of_int (1)) in
       let u = get s.sk t in
       let r =
         push_preds radj s.cc (get roff (add u (Uint63.of_int (1))))
           (get roff u) s.lb s.sk t
       in
       Some { lb = (fst (fst r)); sk = (snd (fst r)); sq = (snd r); ii =
       s.ii; cc = s.cc }
  else if ltb (Uint63.of_int (0)) s.ii
       then let i = sub s.ii (Uint63.of_int (1)) in
            let r = get post i in
            if eqb (get s.lb r) (Uint63.of_int (0))
            then Some { lb = (set s.lb r (add s.cc (Uint63.of_int (1))));
                   sk = (set s.sk (Uint63.of_int (0)) r); sq =
                   (Uint63.of_int (1)); ii = i; cc =
                   (add s.cc (Uint63.of_int (1))) }
            else Some { lb = s.lb; sk = s.sk; sq = s.sq; ii = i; cc = s.cc }
       else None

(** val assign :
    Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t Marray.t -> d2 ->
    Uint63.t -> Uint63.t -> d2 **)

let rec assign roff radj post s bound steps =
  if bdec (ltb steps bound)
  then (match asg_step roff radj post s with
        | Some s' ->
          assign roff radj post s' bound (add steps (Uint63.of_int (1)))
        | None -> s)
  else s

(** val merge_loop :
    (Uint63.t -> Uint63.t -> bool) -> Uint63.t Marray.t -> Uint63.t Marray.t
    -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t
    Marray.t **)

let rec merge_loop le a t mid hi i j k =
  if bdec (ltb k hi)
  then if (&&) (ltb i mid) ((||) (leb hi j) (le (get a i) (get a j)))
       then merge_loop le a (set t k (get a i)) mid hi
              (add i (Uint63.of_int (1))) j (add k (Uint63.of_int (1)))
       else merge_loop le a (set t k (get a j)) mid hi i
              (add j (Uint63.of_int (1))) (add k (Uint63.of_int (1)))
  else t

(** val copy_back :
    Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t ->
    Uint63.t Marray.t **)

let rec copy_back t a hi k =
  if bdec (ltb k hi)
  then copy_back t (set a k (get t k)) hi (add k (Uint63.of_int (1)))
  else a

(** val msort :
    (Uint63.t -> Uint63.t -> bool) -> Uint63.t Marray.t -> Uint63.t Marray.t
    -> Uint63.t -> Uint63.t -> Uint63.t Marray.t * Uint63.t Marray.t **)

let rec msort le a t lo hi =
  if bdec (ltb lo hi)
  then if bdec (ltb (Uint63.of_int (1)) (sub hi lo))
       then let mid = add lo (div (sub hi lo) (Uint63.of_int (2))) in
            let r1 = msort le a t lo mid in
            let r2 = msort le (fst r1) (snd r1) mid hi in
            let t3 = merge_loop le (fst r2) (snd r2) mid hi lo mid lo in
            ((copy_back t3 (fst r2) hi lo), t3)
       else (a, t)
  else (a, t)

(** val iota_loop :
    Uint63.t -> Uint63.t -> Uint63.t Marray.t -> Uint63.t Marray.t **)

let rec iota_loop n k a =
  if bdec (ltb k n)
  then iota_loop n (add k (Uint63.of_int (1))) (set a k k)
  else a

type d3 = { gord : Uint63.t Marray.t; gn : Uint63.t; av : string Marray.t;
            an : Uint63.t }

(** val emit_loop :
    string Marray.t -> Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t
    Marray.t -> Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t ->
    Uint63.t -> d3 -> d3 **)

let rec emit_loop names lab csz boff badj byname v k s =
  if bdec (ltb k v)
  then let v0 = get byname k in
       let c = get lab v0 in
       if ltb (Uint63.of_int (1)) (get csz c)
       then if eqb (get badj (get boff c)) v0
            then emit_loop names lab csz boff badj byname v
                   (add k (Uint63.of_int (1))) { gord = (set s.gord s.gn c);
                   gn = (add s.gn (Uint63.of_int (1))); av = s.av; an = s.an }
            else emit_loop names lab csz boff badj byname v
                   (add k (Uint63.of_int (1))) s
       else emit_loop names lab csz boff badj byname v
              (add k (Uint63.of_int (1))) { gord = s.gord; gn = s.gn; av =
              (set s.av s.an (get names v0)); an =
              (add s.an (Uint63.of_int (1))) }
  else s

(** val copy_loop :
    string Marray.t -> Uint63.t -> Uint63.t -> string Marray.t -> string
    Marray.t **)

let rec copy_loop src n k dst =
  if bdec (ltb k n)
  then copy_loop src n (add k (Uint63.of_int (1))) (set dst k (get src k))
  else dst

(** val inner_loop :
    string Marray.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t
    -> string Marray.t -> string Marray.t **)

let rec inner_loop names badj st n k g =
  if bdec (ltb k n)
  then inner_loop names badj st n (add k (Uint63.of_int (1)))
         (set g k (get names (get badj (add st k))))
  else g

(** val group_arr :
    string Marray.t -> Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t ->
    string Marray.t **)

let group_arr names boff badj c =
  let st = get boff c in
  let n = sub (get boff (add c (Uint63.of_int (1)))) st in
  inner_loop names badj st n (Uint63.of_int (0))
    (make n (make0 (Uint63.of_int (0)) (Uint63.of_int (0))))

(** val groups_loop :
    string Marray.t -> Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t
    Marray.t -> Uint63.t -> Uint63.t -> string Marray.t Marray.t -> string
    Marray.t Marray.t **)

let rec groups_loop names boff badj gord0 g g0 out =
  if bdec (ltb g0 g)
  then groups_loop names boff badj gord0 g (add g0 (Uint63.of_int (1)))
         (set out g0 (group_arr names boff badj (get gord0 g0)))
  else out

(** val name_le : string Marray.t -> Uint63.t -> Uint63.t -> bool **)

let name_le names a b =
  match compare (get names a) (get names b) with
  | Gt -> false
  | _ -> true

(** val empty_str : string **)

let empty_str =
  make0 (Uint63.of_int (0)) (Uint63.of_int (0))

(** val loopy_impl :
    string Marray.t -> string Marray.t -> string Marray.t Marray.t * string
    Marray.t **)

let loopy_impl x y =
  let m = length x in
  let st0 = { ht =
    (make (add (add hsize (mul (Uint63.of_int (2)) m)) (Uint63.of_int (1)))
      (Uint63.of_int (0)));
    hn =
    (make (add (mul (Uint63.of_int (2)) m) (Uint63.of_int (1))) empty_str);
    hc = (Uint63.of_int (0)) }
  in
  let r0 =
    idloop x y m (Uint63.of_int (0)) st0 (make m (Uint63.of_int (0)))
      (make m (Uint63.of_int (0)))
  in
  let st = fst (fst r0) in
  let is = snd (fst r0) in
  let id = snd r0 in
  let v = st.hc in
  let names = st.hn in
  let g = csr v m (fun k -> get is k) (fun k -> get id k) in
  let gt = csr v m (fun k -> get id k) (fun k -> get is k) in
  let bound = add (mul (Uint63.of_int (3)) v) (Uint63.of_int (1)) in
  let post =
    dfs v (fst g) (snd g) { mk = (make v (Uint63.of_int (0))); sv =
      (make v (Uint63.of_int (0))); sc = (make v (Uint63.of_int (0))); po =
      (make v (Uint63.of_int (0))); sp = (Uint63.of_int (0)); np =
      (Uint63.of_int (0)); rt = (Uint63.of_int (0)) } bound
      (Uint63.of_int (0))
  in
  let s2 =
    assign (fst gt) (snd gt) post { lb = (make v (Uint63.of_int (0))); sk =
      (make v (Uint63.of_int (0))); sq = (Uint63.of_int (0)); ii = v; cc =
      (Uint63.of_int (0)) } bound (Uint63.of_int (0))
  in
  let lab = s2.lb in
  let c = s2.cc in
  let csz =
    cnt_loop (fun v0 -> get lab v0) v (Uint63.of_int (0))
      (make (add c (Uint63.of_int (1))) (Uint63.of_int (0)))
  in
  let byname =
    fst
      (msort (name_le names)
        (iota_loop v (Uint63.of_int (0)) (make v (Uint63.of_int (0))))
        (make v (Uint63.of_int (0))) (Uint63.of_int (0)) v)
  in
  let b =
    csr (add c (Uint63.of_int (1))) v (fun k -> get lab (get byname k))
      (fun k -> get byname k)
  in
  let s3 =
    emit_loop names lab csz (fst b) (snd b) byname v (Uint63.of_int (0))
      { gord = (make v (Uint63.of_int (0))); gn = (Uint63.of_int (0)); av =
      (make v empty_str); an = (Uint63.of_int (0)) }
  in
  let avoid = copy_loop s3.av s3.an (Uint63.of_int (0)) (make s3.an empty_str)
  in
  let groups =
    groups_loop names (fst b) (snd b) s3.gord s3.gn (Uint63.of_int (0))
      (make s3.gn (make (Uint63.of_int (0)) empty_str))
  in
  (groups, avoid)

module LoopycabdriversImpl =
 struct
  (** val loopy_regions :
      string Marray.t -> string Marray.t -> string Marray.t Marray.t * string
      Marray.t **)

  let loopy_regions =
    loopy_impl
 end
