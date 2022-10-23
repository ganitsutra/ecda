
type __ = Obj.t

(** val length : 'a1 list -> int **)

let rec length = function
| [] -> 0
| _::l' -> (fun x -> x + 1) (length l')

(** val add : int -> int -> int **)

let rec add = ( + )

(** val sub : int -> int -> int **)

let rec sub = fun n m -> if m>n then 0 else n-m

(** val eqb : int -> int -> bool **)

let rec eqb = ( = )

(** val leb : int -> int -> bool **)

let rec leb = (<=)

(** val ltb : int -> int -> bool **)

let ltb = (<)

type reflect =
| ReflectT
| ReflectF

(** val nth : int -> 'a1 list -> 'a1 -> 'a1 **)

let rec nth n l default =
  (fun zero succ n -> if n=0 then zero () else succ (n-1))
    (fun _ -> match l with
              | [] -> default
              | x::_ -> x)
    (fun m -> match l with
              | [] -> default
              | _::t -> nth m t default)
    n

(** val lt_eq_lt_dec : int -> int -> bool option **)

let rec lt_eq_lt_dec = fun n m -> if n>m then None else Some (n<m)

(** val le_lt_dec : int -> int -> bool **)

let rec le_lt_dec n m =
  (fun zero succ n -> if n=0 then zero () else succ (n-1))
    (fun _ -> true)
    (fun n0 ->
    (fun zero succ n -> if n=0 then zero () else succ (n-1))
      (fun _ -> false)
      (fun m0 -> le_lt_dec n0 m0)
      m)
    n

(** val le_gt_dec : int -> int -> bool **)

let le_gt_dec =
  le_lt_dec

(** val le_dec : int -> int -> bool **)

let le_dec =
  le_gt_dec

(** val lt_dec : int -> int -> bool **)

let lt_dec n m =
  le_dec ((fun x -> x + 1) n) m

(** val reflect_intro : bool -> reflect **)

let reflect_intro = function
| true -> ReflectT
| false -> ReflectF

(** val putin : ('a1 -> 'a1 -> bool) -> 'a1 -> 'a1 list -> 'a1 list **)

let rec putin lr a l = match l with
| [] -> a::[]
| b::l1 -> if lr a b then a::l else b::(putin lr a l1)

(** val sort : ('a1 -> 'a1 -> bool) -> 'a1 list -> 'a1 list **)

let rec sort lr = function
| [] -> []
| a::l1 -> putin lr a (sort lr l1)

module Decidable =
 struct
  type coq_type = { eqb : (__ -> __ -> bool); eqP : (__ -> __ -> reflect) }

  type coq_E = __

  (** val eqb : coq_type -> coq_E -> coq_E -> bool **)

  let eqb t =
    t.eqb
 end

(** val nat_eqP : int -> int -> reflect **)

let nat_eqP x y =
  reflect_intro (eqb x y)

(** val nat_eqType : Decidable.coq_type **)

let nat_eqType =
  { Decidable.eqb = (Obj.magic eqb); Decidable.eqP = (Obj.magic nat_eqP) }

(** val memb :
    Decidable.coq_type -> Decidable.coq_E -> Decidable.coq_E list -> bool **)

let rec memb a a0 = function
| [] -> false
| a1::l1 -> (||) (a.Decidable.eqb a0 a1) (memb a a0 l1)

(** val uniq :
    Decidable.coq_type -> Decidable.coq_E list -> Decidable.coq_E list **)

let rec uniq a = function
| [] -> []
| h::x1 -> if memb a h x1 then uniq a x1 else h::(uniq a x1)

type order = { id : int; otime : int; oquantity : int; oprice : int }

(** val w0 : order **)

let w0 =
  { id = 0; otime = 0; oquantity = ((fun x -> x + 1) 0); oprice = 0 }

(** val delete_order : order list -> int -> order list **)

let rec delete_order b i =
  match b with
  | [] -> []
  | b0::b' ->
    if nat_eqType.Decidable.eqb (Obj.magic b0.id) (Obj.magic i)
    then delete_order b' i
    else b0::(delete_order b' i)

type transaction = { idb : int; ida : int; tquantity : int }

(** val t_eqb : transaction -> transaction -> bool **)

let t_eqb x y =
  (&&)
    ((&&) (nat_eqType.Decidable.eqb (Obj.magic x.idb) (Obj.magic y.idb))
      (nat_eqType.Decidable.eqb (Obj.magic x.ida) (Obj.magic y.ida)))
    (nat_eqType.Decidable.eqb (Obj.magic x.tquantity) (Obj.magic y.tquantity))

(** val t_eqP : transaction -> transaction -> reflect **)

let t_eqP x y =
  reflect_intro (t_eqb x y)

(** val transact_eqType : Decidable.coq_type **)

let transact_eqType =
  { Decidable.eqb = (Obj.magic t_eqb); Decidable.eqP = (Obj.magic t_eqP) }

(** val blist : ((order list*order list)*transaction list) -> order list **)

let blist = function
| p0,_ -> let x,_ = p0 in x

(** val alist : ((order list*order list)*transaction list) -> order list **)

let alist = function
| p0,_ -> let _,y = p0 in y

(** val mlist :
    ((order list*order list)*transaction list) -> transaction list **)

let mlist = function
| _,z -> z

(** val qty : transaction list -> int -> int -> int **)

let rec qty t i1 i2 =
  match t with
  | [] -> 0
  | t0::t' ->
    if (&&) (nat_eqType.Decidable.eqb (Obj.magic t0.idb) (Obj.magic i1))
         (nat_eqType.Decidable.eqb (Obj.magic t0.ida) (Obj.magic i2))
    then add t0.tquantity (qty t' i1 i2)
    else qty t' i1 i2

(** val ids_bid_aux : transaction list -> int list **)

let rec ids_bid_aux = function
| [] -> []
| t1::t' -> t1.idb::(ids_bid_aux t')

(** val ids_ask_aux : transaction list -> int list **)

let rec ids_ask_aux = function
| [] -> []
| t1::t' -> t1.ida::(ids_ask_aux t')

(** val cform_aux :
    transaction list -> int list -> int list -> transaction list **)

let rec cform_aux t bi ai =
  match bi with
  | [] -> []
  | i::bi' ->
    (match ai with
     | [] -> []
     | j::ai' ->
       if lt_dec (qty t i j) ((fun x -> x + 1) 0)
       then cform_aux t bi' ai'
       else { idb = i; ida = j; tquantity =
              (qty t i j) }::(cform_aux t bi' ai'))

(** val cform : transaction list -> transaction list **)

let cform m =
  Obj.magic uniq transact_eqType (cform_aux m (ids_bid_aux m) (ids_ask_aux m))

(** val bcompetitive : order -> order -> bool **)

let bcompetitive b b' =
  (||) (ltb b'.oprice b.oprice)
    ((&&) (eqb b'.oprice b.oprice) (leb b.otime b'.otime))

(** val acompetitive : order -> order -> bool **)

let acompetitive a a' =
  (||) (ltb a.oprice a'.oprice)
    ((&&) (eqb a.oprice a'.oprice) (leb a.otime a'.otime))

type command =
| Buy
| Sell
| Del

type instruction = { cmd : command; ord : order }

(** val action0 : command **)

let action0 =
  Del

(** val tau0 : instruction **)

let tau0 =
  { cmd = action0; ord = w0 }

(** val iterate :
    (order list -> order list -> instruction -> (order list*order
    list)*transaction list) -> instruction list -> int -> (order list*order
    list)*transaction list **)

let rec iterate p i k =
  (fun zero succ n -> if n=0 then zero () else succ (n-1))
    (fun _ -> ([],[]),[])
    (fun k' ->
    let it = iterate p i k' in p (blist it) (alist it) (nth k' i tau0))
    k

(** val iterated :
    (order list -> order list -> instruction -> (order list*order
    list)*transaction list) -> instruction list -> int -> (order list*order
    list)*transaction list **)

let iterated p i k =
  if ltb (length i) k then ([],[]),[] else iterate p i k

(** val match_ask :
    order list -> order list -> order -> (order list*order list)*transaction
    list **)

let rec match_ask b a a0 =
  match b with
  | [] -> ([],(a0::a)),[]
  | b0::b' ->
    let n = sub a0.oprice b0.oprice in
    ((fun zero succ n -> if n=0 then zero () else succ (n-1))
       (fun _ ->
       match lt_eq_lt_dec b0.oquantity a0.oquantity with
       | Some s ->
         if s
         then let bAM =
                match_ask b' a { id = a0.id; otime = a0.otime; oquantity =
                  (sub a0.oquantity b0.oquantity); oprice = a0.oprice }
              in
              ((blist bAM),(alist bAM)),({ idb = b0.id; ida = a0.id;
              tquantity = b0.oquantity }::(mlist bAM))
         else (b',a),({ idb = b0.id; ida = a0.id; tquantity =
                a0.oquantity }::[])
       | None ->
         (({ id = b0.id; otime = b0.otime; oquantity =
           (sub b0.oquantity a0.oquantity); oprice =
           b0.oprice }::b'),a),({ idb = b0.id; ida = a0.id; tquantity =
           a0.oquantity }::[]))
       (fun _ -> ((b0::b'),(a0::a)),[])
       n)

(** val match_bid :
    order list -> order list -> order -> (order list*order list)*transaction
    list **)

let rec match_bid b a b0 =
  match a with
  | [] -> ((b0::b),[]),[]
  | a0::a' ->
    let n = sub a0.oprice b0.oprice in
    ((fun zero succ n -> if n=0 then zero () else succ (n-1))
       (fun _ ->
       match lt_eq_lt_dec b0.oquantity a0.oquantity with
       | Some s ->
         if s
         then (b,({ id = a0.id; otime = a0.otime; oquantity =
                (sub a0.oquantity b0.oquantity); oprice =
                a0.oprice }::a')),({ idb = b0.id; ida = a0.id; tquantity =
                b0.oquantity }::[])
         else (b,a'),({ idb = b0.id; ida = a0.id; tquantity =
                b0.oquantity }::[])
       | None ->
         let bAM =
           match_bid b a' { id = b0.id; otime = b0.otime; oquantity =
             (sub b0.oquantity a0.oquantity); oprice = b0.oprice }
         in
         ((blist bAM),(alist bAM)),({ idb = b0.id; ida = a0.id; tquantity =
         a0.oquantity }::(mlist bAM)))
       (fun _ -> ((b0::b),(a0::a')),[])
       n)

(** val del_order :
    order list -> order list -> int -> (order list*order list)*transaction
    list **)

let del_order b a i =
  ((delete_order b i),(delete_order a i)),[]

(** val process_instruction :
    order list -> order list -> instruction -> (order list*order
    list)*transaction list **)

let process_instruction b a tau =
  match tau.cmd with
  | Buy -> match_bid b (sort acompetitive a) tau.ord
  | Sell -> match_ask (sort bcompetitive b) a tau.ord
  | Del -> del_order b a tau.ord.id

(** val main :
    instruction list -> int -> (order list*order list)*transaction list **)

let main i k =
  iterated process_instruction i k
