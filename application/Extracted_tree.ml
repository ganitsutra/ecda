
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

type reflect =
| ReflectT
| ReflectF

module Nat =
 struct
  (** val eqb : int -> int -> bool **)

  let rec eqb = ( = )

  (** val leb : int -> int -> bool **)

  let rec leb = (<=)

  (** val ltb : int -> int -> bool **)

  let ltb = (<)
 end

(** val nth : int -> 'a1 list -> 'a1 -> 'a1 **)

let rec nth n l default =
  (fun zero succ n -> if n=0 then zero () else succ (n-1))
    (fun _ -> match l with
              | [] -> default
              | x::_ -> x)
    (fun m -> match l with
              | [] -> default
              | _::t0 -> nth m t0 default)
    n

type color =
| Red
| Black

module Color =
 struct
  type t = color
 end

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

module Decidable =
 struct
  type coq_type = { eqb : (__ -> __ -> bool); eqP : (__ -> __ -> reflect) }

  type coq_E = __

  (** val eqb : coq_type -> coq_E -> coq_E -> bool **)

  let eqb t0 =
    t0.eqb
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

(** val qty : transaction list -> int -> int -> int **)

let rec qty t0 i1 i2 =
  match t0 with
  | [] -> 0
  | t1::t' ->
    if (&&) (nat_eqType.Decidable.eqb (Obj.magic t1.idb) (Obj.magic i1))
         (nat_eqType.Decidable.eqb (Obj.magic t1.ida) (Obj.magic i2))
    then add t1.tquantity (qty t' i1 i2)
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

let rec cform_aux t0 bi ai =
  match bi with
  | [] -> []
  | i::bi' ->
    (match ai with
     | [] -> []
     | j::ai' ->
       if lt_dec (qty t0 i j) ((fun x -> x + 1) 0)
       then cform_aux t0 bi' ai'
       else { idb = i; ida = j; tquantity =
              (qty t0 i j) }::(cform_aux t0 bi' ai'))

(** val cform : transaction list -> transaction list **)

let cform m =
  Obj.magic uniq transact_eqType (cform_aux m (ids_bid_aux m) (ids_ask_aux m))

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

module TB =
 struct
  type elt = order

  type tree =
  | Leaf
  | Node of Color.t * tree * order * tree

  (** val empty : tree **)

  let empty =
    Leaf

  (** val max_elt : tree -> elt option **)

  let rec max_elt = function
  | Leaf -> None
  | Node (_, _, x, r) ->
    (match r with
     | Leaf -> Some x
     | Node (_, _, _, _) -> max_elt r)

  type t = tree

  (** val makeBlack : tree -> tree **)

  let makeBlack = function
  | Leaf -> Leaf
  | Node (_, a, x, b) -> Node (Black, a, x, b)

  (** val makeRed : tree -> tree **)

  let makeRed = function
  | Leaf -> Leaf
  | Node (_, a, x, b) -> Node (Red, a, x, b)

  (** val lbal : tree -> order -> tree -> tree **)

  let lbal l k r =
    match l with
    | Leaf -> Node (Black, l, k, r)
    | Node (t0, a, x, c) ->
      (match t0 with
       | Red ->
         (match a with
          | Leaf ->
            (match c with
             | Leaf -> Node (Black, l, k, r)
             | Node (t1, b, y, c0) ->
               (match t1 with
                | Red ->
                  Node (Red, (Node (Black, a, x, b)), y, (Node (Black, c0, k,
                    r)))
                | Black -> Node (Black, l, k, r)))
          | Node (t1, a0, x0, b) ->
            (match t1 with
             | Red ->
               Node (Red, (Node (Black, a0, x0, b)), x, (Node (Black, c, k,
                 r)))
             | Black ->
               (match c with
                | Leaf -> Node (Black, l, k, r)
                | Node (t2, b0, y, c0) ->
                  (match t2 with
                   | Red ->
                     Node (Red, (Node (Black, a, x, b0)), y, (Node (Black,
                       c0, k, r)))
                   | Black -> Node (Black, l, k, r)))))
       | Black -> Node (Black, l, k, r))

  (** val rbal : tree -> order -> tree -> tree **)

  let rbal l k r = match r with
  | Leaf -> Node (Black, l, k, r)
  | Node (t0, b, y, d) ->
    (match t0 with
     | Red ->
       (match b with
        | Leaf ->
          (match d with
           | Leaf -> Node (Black, l, k, r)
           | Node (t1, c, z, d0) ->
             (match t1 with
              | Red ->
                Node (Red, (Node (Black, l, k, b)), y, (Node (Black, c, z,
                  d0)))
              | Black -> Node (Black, l, k, r)))
        | Node (t1, b0, y0, c) ->
          (match t1 with
           | Red ->
             Node (Red, (Node (Black, l, k, b0)), y0, (Node (Black, c, y, d)))
           | Black ->
             (match d with
              | Leaf -> Node (Black, l, k, r)
              | Node (t2, c0, z, d0) ->
                (match t2 with
                 | Red ->
                   Node (Red, (Node (Black, l, k, b)), y, (Node (Black, c0,
                     z, d0)))
                 | Black -> Node (Black, l, k, r)))))
     | Black -> Node (Black, l, k, r))

  (** val rbal' : tree -> order -> tree -> tree **)

  let rbal' l k r = match r with
  | Leaf -> Node (Black, l, k, r)
  | Node (t0, b, z, d) ->
    (match t0 with
     | Red ->
       (match b with
        | Leaf ->
          (match d with
           | Leaf -> Node (Black, l, k, r)
           | Node (t1, c, z0, d0) ->
             (match t1 with
              | Red ->
                Node (Red, (Node (Black, l, k, b)), z, (Node (Black, c, z0,
                  d0)))
              | Black -> Node (Black, l, k, r)))
        | Node (t1, b0, y, c) ->
          (match t1 with
           | Red ->
             (match d with
              | Leaf ->
                Node (Red, (Node (Black, l, k, b0)), y, (Node (Black, c, z,
                  d)))
              | Node (t2, c0, z0, d0) ->
                (match t2 with
                 | Red ->
                   Node (Red, (Node (Black, l, k, b)), z, (Node (Black, c0,
                     z0, d0)))
                 | Black ->
                   Node (Red, (Node (Black, l, k, b0)), y, (Node (Black, c,
                     z, d)))))
           | Black ->
             (match d with
              | Leaf -> Node (Black, l, k, r)
              | Node (t2, c0, z0, d0) ->
                (match t2 with
                 | Red ->
                   Node (Red, (Node (Black, l, k, b)), z, (Node (Black, c0,
                     z0, d0)))
                 | Black -> Node (Black, l, k, r)))))
     | Black -> Node (Black, l, k, r))

  (** val lbalS : tree -> order -> tree -> tree **)

  let lbalS l k r =
    match l with
    | Leaf ->
      (match r with
       | Leaf -> Node (Red, l, k, r)
       | Node (t0, a, z, c) ->
         (match t0 with
          | Red ->
            (match a with
             | Leaf -> Node (Red, l, k, r)
             | Node (t1, a0, y, b) ->
               (match t1 with
                | Red -> Node (Red, l, k, r)
                | Black ->
                  Node (Red, (Node (Black, l, k, a0)), y,
                    (rbal' b z (makeRed c)))))
          | Black -> rbal' l k (Node (Red, a, z, c))))
    | Node (t0, a, x, b) ->
      (match t0 with
       | Red -> Node (Red, (Node (Black, a, x, b)), k, r)
       | Black ->
         (match r with
          | Leaf -> Node (Red, l, k, r)
          | Node (t1, a0, z, c) ->
            (match t1 with
             | Red ->
               (match a0 with
                | Leaf -> Node (Red, l, k, r)
                | Node (t2, a1, y, b0) ->
                  (match t2 with
                   | Red -> Node (Red, l, k, r)
                   | Black ->
                     Node (Red, (Node (Black, l, k, a1)), y,
                       (rbal' b0 z (makeRed c)))))
             | Black -> rbal' l k (Node (Red, a0, z, c)))))

  (** val rbalS : tree -> order -> tree -> tree **)

  let rbalS l k r = match r with
  | Leaf ->
    (match l with
     | Leaf -> Node (Red, l, k, r)
     | Node (t0, a, x, b) ->
       (match t0 with
        | Red ->
          (match b with
           | Leaf -> Node (Red, l, k, r)
           | Node (t1, b0, y, c) ->
             (match t1 with
              | Red -> Node (Red, l, k, r)
              | Black ->
                Node (Red, (lbal (makeRed a) x b0), y, (Node (Black, c, k,
                  r)))))
        | Black -> lbal (Node (Red, a, x, b)) k r))
  | Node (t0, b, y, c) ->
    (match t0 with
     | Red -> Node (Red, l, k, (Node (Black, b, y, c)))
     | Black ->
       (match l with
        | Leaf -> Node (Red, l, k, r)
        | Node (t1, a, x, b0) ->
          (match t1 with
           | Red ->
             (match b0 with
              | Leaf -> Node (Red, l, k, r)
              | Node (t2, b1, y0, c0) ->
                (match t2 with
                 | Red -> Node (Red, l, k, r)
                 | Black ->
                   Node (Red, (lbal (makeRed a) x b1), y0, (Node (Black, c0,
                     k, r)))))
           | Black -> lbal (Node (Red, a, x, b0)) k r)))

  (** val ins : order -> tree -> tree **)

  let rec ins x s = match s with
  | Leaf -> Node (Red, Leaf, x, Leaf)
  | Node (c, l, y, r) ->
    if (&&) (Nat.eqb x.oprice y.oprice) (Nat.eqb x.otime y.otime)
    then s
    else if (||) (Nat.ltb x.oprice y.oprice)
              ((&&) (Nat.eqb x.oprice y.oprice) (Nat.ltb y.otime x.otime))
         then (match c with
               | Red -> Node (Red, (ins x l), y, r)
               | Black -> lbal (ins x l) y r)
         else (match c with
               | Red -> Node (Red, l, y, (ins x r))
               | Black -> rbal l y (ins x r))

  (** val add : order -> tree -> tree **)

  let add x s =
    makeBlack (ins x s)

  (** val append : tree -> tree -> tree **)

  let rec append l = match l with
  | Leaf -> (fun r -> r)
  | Node (lc, ll, lx, lr) ->
    let rec append_l r = match r with
    | Leaf -> l
    | Node (rc, rl, rx, rr) ->
      (match lc with
       | Red ->
         (match rc with
          | Red ->
            let lrl = append lr rl in
            (match lrl with
             | Leaf -> Node (Red, ll, lx, (Node (Red, lrl, rx, rr)))
             | Node (t0, lr', x, rl') ->
               (match t0 with
                | Red ->
                  Node (Red, (Node (Red, ll, lx, lr')), x, (Node (Red, rl',
                    rx, rr)))
                | Black -> Node (Red, ll, lx, (Node (Red, lrl, rx, rr)))))
          | Black -> Node (Red, ll, lx, (append lr r)))
       | Black ->
         (match rc with
          | Red -> Node (Red, (append_l rl), rx, rr)
          | Black ->
            let lrl = append lr rl in
            (match lrl with
             | Leaf -> lbalS ll lx (Node (Black, lrl, rx, rr))
             | Node (t0, lr', x, rl') ->
               (match t0 with
                | Red ->
                  Node (Red, (Node (Black, ll, lx, lr')), x, (Node (Black,
                    rl', rx, rr)))
                | Black -> lbalS ll lx (Node (Black, lrl, rx, rr))))))
    in append_l

  (** val del : order -> tree -> tree **)

  let rec del x = function
  | Leaf -> Leaf
  | Node (_, a, y, b) ->
    if (&&) (Nat.eqb x.oprice y.oprice) (Nat.eqb x.otime y.otime)
    then append a b
    else if (||) (Nat.ltb x.oprice y.oprice)
              ((&&) (Nat.eqb x.oprice y.oprice) (Nat.ltb y.otime x.otime))
         then (match a with
               | Leaf -> Node (Red, (del x a), y, b)
               | Node (t1, _, _, _) ->
                 (match t1 with
                  | Red -> Node (Red, (del x a), y, b)
                  | Black -> lbalS (del x a) y b))
         else (match b with
               | Leaf -> Node (Red, a, y, (del x b))
               | Node (t1, _, _, _) ->
                 (match t1 with
                  | Red -> Node (Red, a, y, (del x b))
                  | Black -> rbalS a y (del x b)))

  (** val remove : order -> tree -> tree **)

  let remove x t0 =
    makeBlack (del x t0)
 end

module TA =
 struct
  type elt = order

  type tree =
  | Leaf
  | Node of Color.t * tree * order * tree

  (** val empty : tree **)

  let empty =
    Leaf

  (** val max_elt : tree -> elt option **)

  let rec max_elt = function
  | Leaf -> None
  | Node (_, _, x, r) ->
    (match r with
     | Leaf -> Some x
     | Node (_, _, _, _) -> max_elt r)

  type t = tree

  (** val makeBlack : tree -> tree **)

  let makeBlack = function
  | Leaf -> Leaf
  | Node (_, a, x, b) -> Node (Black, a, x, b)

  (** val makeRed : tree -> tree **)

  let makeRed = function
  | Leaf -> Leaf
  | Node (_, a, x, b) -> Node (Red, a, x, b)

  (** val lbal : tree -> order -> tree -> tree **)

  let lbal l k r =
    match l with
    | Leaf -> Node (Black, l, k, r)
    | Node (t0, a, x, c) ->
      (match t0 with
       | Red ->
         (match a with
          | Leaf ->
            (match c with
             | Leaf -> Node (Black, l, k, r)
             | Node (t1, b, y, c0) ->
               (match t1 with
                | Red ->
                  Node (Red, (Node (Black, a, x, b)), y, (Node (Black, c0, k,
                    r)))
                | Black -> Node (Black, l, k, r)))
          | Node (t1, a0, x0, b) ->
            (match t1 with
             | Red ->
               Node (Red, (Node (Black, a0, x0, b)), x, (Node (Black, c, k,
                 r)))
             | Black ->
               (match c with
                | Leaf -> Node (Black, l, k, r)
                | Node (t2, b0, y, c0) ->
                  (match t2 with
                   | Red ->
                     Node (Red, (Node (Black, a, x, b0)), y, (Node (Black,
                       c0, k, r)))
                   | Black -> Node (Black, l, k, r)))))
       | Black -> Node (Black, l, k, r))

  (** val rbal : tree -> order -> tree -> tree **)

  let rbal l k r = match r with
  | Leaf -> Node (Black, l, k, r)
  | Node (t0, b, y, d) ->
    (match t0 with
     | Red ->
       (match b with
        | Leaf ->
          (match d with
           | Leaf -> Node (Black, l, k, r)
           | Node (t1, c, z, d0) ->
             (match t1 with
              | Red ->
                Node (Red, (Node (Black, l, k, b)), y, (Node (Black, c, z,
                  d0)))
              | Black -> Node (Black, l, k, r)))
        | Node (t1, b0, y0, c) ->
          (match t1 with
           | Red ->
             Node (Red, (Node (Black, l, k, b0)), y0, (Node (Black, c, y, d)))
           | Black ->
             (match d with
              | Leaf -> Node (Black, l, k, r)
              | Node (t2, c0, z, d0) ->
                (match t2 with
                 | Red ->
                   Node (Red, (Node (Black, l, k, b)), y, (Node (Black, c0,
                     z, d0)))
                 | Black -> Node (Black, l, k, r)))))
     | Black -> Node (Black, l, k, r))

  (** val rbal' : tree -> order -> tree -> tree **)

  let rbal' l k r = match r with
  | Leaf -> Node (Black, l, k, r)
  | Node (t0, b, z, d) ->
    (match t0 with
     | Red ->
       (match b with
        | Leaf ->
          (match d with
           | Leaf -> Node (Black, l, k, r)
           | Node (t1, c, z0, d0) ->
             (match t1 with
              | Red ->
                Node (Red, (Node (Black, l, k, b)), z, (Node (Black, c, z0,
                  d0)))
              | Black -> Node (Black, l, k, r)))
        | Node (t1, b0, y, c) ->
          (match t1 with
           | Red ->
             (match d with
              | Leaf ->
                Node (Red, (Node (Black, l, k, b0)), y, (Node (Black, c, z,
                  d)))
              | Node (t2, c0, z0, d0) ->
                (match t2 with
                 | Red ->
                   Node (Red, (Node (Black, l, k, b)), z, (Node (Black, c0,
                     z0, d0)))
                 | Black ->
                   Node (Red, (Node (Black, l, k, b0)), y, (Node (Black, c,
                     z, d)))))
           | Black ->
             (match d with
              | Leaf -> Node (Black, l, k, r)
              | Node (t2, c0, z0, d0) ->
                (match t2 with
                 | Red ->
                   Node (Red, (Node (Black, l, k, b)), z, (Node (Black, c0,
                     z0, d0)))
                 | Black -> Node (Black, l, k, r)))))
     | Black -> Node (Black, l, k, r))

  (** val lbalS : tree -> order -> tree -> tree **)

  let lbalS l k r =
    match l with
    | Leaf ->
      (match r with
       | Leaf -> Node (Red, l, k, r)
       | Node (t0, a, z, c) ->
         (match t0 with
          | Red ->
            (match a with
             | Leaf -> Node (Red, l, k, r)
             | Node (t1, a0, y, b) ->
               (match t1 with
                | Red -> Node (Red, l, k, r)
                | Black ->
                  Node (Red, (Node (Black, l, k, a0)), y,
                    (rbal' b z (makeRed c)))))
          | Black -> rbal' l k (Node (Red, a, z, c))))
    | Node (t0, a, x, b) ->
      (match t0 with
       | Red -> Node (Red, (Node (Black, a, x, b)), k, r)
       | Black ->
         (match r with
          | Leaf -> Node (Red, l, k, r)
          | Node (t1, a0, z, c) ->
            (match t1 with
             | Red ->
               (match a0 with
                | Leaf -> Node (Red, l, k, r)
                | Node (t2, a1, y, b0) ->
                  (match t2 with
                   | Red -> Node (Red, l, k, r)
                   | Black ->
                     Node (Red, (Node (Black, l, k, a1)), y,
                       (rbal' b0 z (makeRed c)))))
             | Black -> rbal' l k (Node (Red, a0, z, c)))))

  (** val rbalS : tree -> order -> tree -> tree **)

  let rbalS l k r = match r with
  | Leaf ->
    (match l with
     | Leaf -> Node (Red, l, k, r)
     | Node (t0, a, x, b) ->
       (match t0 with
        | Red ->
          (match b with
           | Leaf -> Node (Red, l, k, r)
           | Node (t1, b0, y, c) ->
             (match t1 with
              | Red -> Node (Red, l, k, r)
              | Black ->
                Node (Red, (lbal (makeRed a) x b0), y, (Node (Black, c, k,
                  r)))))
        | Black -> lbal (Node (Red, a, x, b)) k r))
  | Node (t0, b, y, c) ->
    (match t0 with
     | Red -> Node (Red, l, k, (Node (Black, b, y, c)))
     | Black ->
       (match l with
        | Leaf -> Node (Red, l, k, r)
        | Node (t1, a, x, b0) ->
          (match t1 with
           | Red ->
             (match b0 with
              | Leaf -> Node (Red, l, k, r)
              | Node (t2, b1, y0, c0) ->
                (match t2 with
                 | Red -> Node (Red, l, k, r)
                 | Black ->
                   Node (Red, (lbal (makeRed a) x b1), y0, (Node (Black, c0,
                     k, r)))))
           | Black -> lbal (Node (Red, a, x, b0)) k r)))

  (** val ins : order -> tree -> tree **)

  let rec ins x s = match s with
  | Leaf -> Node (Red, Leaf, x, Leaf)
  | Node (c, l, y, r) ->
    if (&&) (Nat.eqb x.oprice y.oprice) (Nat.eqb x.otime y.otime)
    then s
    else if (||) (Nat.ltb y.oprice x.oprice)
              ((&&) (Nat.eqb x.oprice y.oprice) (Nat.ltb y.otime x.otime))
         then (match c with
               | Red -> Node (Red, (ins x l), y, r)
               | Black -> lbal (ins x l) y r)
         else (match c with
               | Red -> Node (Red, l, y, (ins x r))
               | Black -> rbal l y (ins x r))

  (** val add : order -> tree -> tree **)

  let add x s =
    makeBlack (ins x s)

  (** val append : tree -> tree -> tree **)

  let rec append l = match l with
  | Leaf -> (fun r -> r)
  | Node (lc, ll, lx, lr) ->
    let rec append_l r = match r with
    | Leaf -> l
    | Node (rc, rl, rx, rr) ->
      (match lc with
       | Red ->
         (match rc with
          | Red ->
            let lrl = append lr rl in
            (match lrl with
             | Leaf -> Node (Red, ll, lx, (Node (Red, lrl, rx, rr)))
             | Node (t0, lr', x, rl') ->
               (match t0 with
                | Red ->
                  Node (Red, (Node (Red, ll, lx, lr')), x, (Node (Red, rl',
                    rx, rr)))
                | Black -> Node (Red, ll, lx, (Node (Red, lrl, rx, rr)))))
          | Black -> Node (Red, ll, lx, (append lr r)))
       | Black ->
         (match rc with
          | Red -> Node (Red, (append_l rl), rx, rr)
          | Black ->
            let lrl = append lr rl in
            (match lrl with
             | Leaf -> lbalS ll lx (Node (Black, lrl, rx, rr))
             | Node (t0, lr', x, rl') ->
               (match t0 with
                | Red ->
                  Node (Red, (Node (Black, ll, lx, lr')), x, (Node (Black,
                    rl', rx, rr)))
                | Black -> lbalS ll lx (Node (Black, lrl, rx, rr))))))
    in append_l

  (** val del : order -> tree -> tree **)

  let rec del x = function
  | Leaf -> Leaf
  | Node (_, a, y, b) ->
    if (&&) (Nat.eqb x.oprice y.oprice) (Nat.eqb x.otime y.otime)
    then append a b
    else if (||) (Nat.ltb y.oprice x.oprice)
              ((&&) (Nat.eqb x.oprice y.oprice) (Nat.ltb y.otime x.otime))
         then (match a with
               | Leaf -> Node (Red, (del x a), y, b)
               | Node (t1, _, _, _) ->
                 (match t1 with
                  | Red -> Node (Red, (del x a), y, b)
                  | Black -> lbalS (del x a) y b))
         else (match b with
               | Leaf -> Node (Red, a, y, (del x b))
               | Node (t1, _, _, _) ->
                 (match t1 with
                  | Red -> Node (Red, a, y, (del x b))
                  | Black -> rbalS a y (del x b)))

  (** val remove : order -> tree -> tree **)

  let remove x t0 =
    makeBlack (del x t0)
 end

module T_id =
 struct
  type elt = order

  type tree =
  | Leaf
  | Node of Color.t * tree * order * tree

  (** val empty : tree **)

  let empty =
    Leaf

  type t = tree

  (** val makeBlack : tree -> tree **)

  let makeBlack = function
  | Leaf -> Leaf
  | Node (_, a, x, b) -> Node (Black, a, x, b)

  (** val makeRed : tree -> tree **)

  let makeRed = function
  | Leaf -> Leaf
  | Node (_, a, x, b) -> Node (Red, a, x, b)

  (** val lbal : tree -> order -> tree -> tree **)

  let lbal l k r =
    match l with
    | Leaf -> Node (Black, l, k, r)
    | Node (t0, a, x, c) ->
      (match t0 with
       | Red ->
         (match a with
          | Leaf ->
            (match c with
             | Leaf -> Node (Black, l, k, r)
             | Node (t1, b, y, c0) ->
               (match t1 with
                | Red ->
                  Node (Red, (Node (Black, a, x, b)), y, (Node (Black, c0, k,
                    r)))
                | Black -> Node (Black, l, k, r)))
          | Node (t1, a0, x0, b) ->
            (match t1 with
             | Red ->
               Node (Red, (Node (Black, a0, x0, b)), x, (Node (Black, c, k,
                 r)))
             | Black ->
               (match c with
                | Leaf -> Node (Black, l, k, r)
                | Node (t2, b0, y, c0) ->
                  (match t2 with
                   | Red ->
                     Node (Red, (Node (Black, a, x, b0)), y, (Node (Black,
                       c0, k, r)))
                   | Black -> Node (Black, l, k, r)))))
       | Black -> Node (Black, l, k, r))

  (** val rbal : tree -> order -> tree -> tree **)

  let rbal l k r = match r with
  | Leaf -> Node (Black, l, k, r)
  | Node (t0, b, y, d) ->
    (match t0 with
     | Red ->
       (match b with
        | Leaf ->
          (match d with
           | Leaf -> Node (Black, l, k, r)
           | Node (t1, c, z, d0) ->
             (match t1 with
              | Red ->
                Node (Red, (Node (Black, l, k, b)), y, (Node (Black, c, z,
                  d0)))
              | Black -> Node (Black, l, k, r)))
        | Node (t1, b0, y0, c) ->
          (match t1 with
           | Red ->
             Node (Red, (Node (Black, l, k, b0)), y0, (Node (Black, c, y, d)))
           | Black ->
             (match d with
              | Leaf -> Node (Black, l, k, r)
              | Node (t2, c0, z, d0) ->
                (match t2 with
                 | Red ->
                   Node (Red, (Node (Black, l, k, b)), y, (Node (Black, c0,
                     z, d0)))
                 | Black -> Node (Black, l, k, r)))))
     | Black -> Node (Black, l, k, r))

  (** val rbal' : tree -> order -> tree -> tree **)

  let rbal' l k r = match r with
  | Leaf -> Node (Black, l, k, r)
  | Node (t0, b, z, d) ->
    (match t0 with
     | Red ->
       (match b with
        | Leaf ->
          (match d with
           | Leaf -> Node (Black, l, k, r)
           | Node (t1, c, z0, d0) ->
             (match t1 with
              | Red ->
                Node (Red, (Node (Black, l, k, b)), z, (Node (Black, c, z0,
                  d0)))
              | Black -> Node (Black, l, k, r)))
        | Node (t1, b0, y, c) ->
          (match t1 with
           | Red ->
             (match d with
              | Leaf ->
                Node (Red, (Node (Black, l, k, b0)), y, (Node (Black, c, z,
                  d)))
              | Node (t2, c0, z0, d0) ->
                (match t2 with
                 | Red ->
                   Node (Red, (Node (Black, l, k, b)), z, (Node (Black, c0,
                     z0, d0)))
                 | Black ->
                   Node (Red, (Node (Black, l, k, b0)), y, (Node (Black, c,
                     z, d)))))
           | Black ->
             (match d with
              | Leaf -> Node (Black, l, k, r)
              | Node (t2, c0, z0, d0) ->
                (match t2 with
                 | Red ->
                   Node (Red, (Node (Black, l, k, b)), z, (Node (Black, c0,
                     z0, d0)))
                 | Black -> Node (Black, l, k, r)))))
     | Black -> Node (Black, l, k, r))

  (** val lbalS : tree -> order -> tree -> tree **)

  let lbalS l k r =
    match l with
    | Leaf ->
      (match r with
       | Leaf -> Node (Red, l, k, r)
       | Node (t0, a, z, c) ->
         (match t0 with
          | Red ->
            (match a with
             | Leaf -> Node (Red, l, k, r)
             | Node (t1, a0, y, b) ->
               (match t1 with
                | Red -> Node (Red, l, k, r)
                | Black ->
                  Node (Red, (Node (Black, l, k, a0)), y,
                    (rbal' b z (makeRed c)))))
          | Black -> rbal' l k (Node (Red, a, z, c))))
    | Node (t0, a, x, b) ->
      (match t0 with
       | Red -> Node (Red, (Node (Black, a, x, b)), k, r)
       | Black ->
         (match r with
          | Leaf -> Node (Red, l, k, r)
          | Node (t1, a0, z, c) ->
            (match t1 with
             | Red ->
               (match a0 with
                | Leaf -> Node (Red, l, k, r)
                | Node (t2, a1, y, b0) ->
                  (match t2 with
                   | Red -> Node (Red, l, k, r)
                   | Black ->
                     Node (Red, (Node (Black, l, k, a1)), y,
                       (rbal' b0 z (makeRed c)))))
             | Black -> rbal' l k (Node (Red, a0, z, c)))))

  (** val rbalS : tree -> order -> tree -> tree **)

  let rbalS l k r = match r with
  | Leaf ->
    (match l with
     | Leaf -> Node (Red, l, k, r)
     | Node (t0, a, x, b) ->
       (match t0 with
        | Red ->
          (match b with
           | Leaf -> Node (Red, l, k, r)
           | Node (t1, b0, y, c) ->
             (match t1 with
              | Red -> Node (Red, l, k, r)
              | Black ->
                Node (Red, (lbal (makeRed a) x b0), y, (Node (Black, c, k,
                  r)))))
        | Black -> lbal (Node (Red, a, x, b)) k r))
  | Node (t0, b, y, c) ->
    (match t0 with
     | Red -> Node (Red, l, k, (Node (Black, b, y, c)))
     | Black ->
       (match l with
        | Leaf -> Node (Red, l, k, r)
        | Node (t1, a, x, b0) ->
          (match t1 with
           | Red ->
             (match b0 with
              | Leaf -> Node (Red, l, k, r)
              | Node (t2, b1, y0, c0) ->
                (match t2 with
                 | Red -> Node (Red, l, k, r)
                 | Black ->
                   Node (Red, (lbal (makeRed a) x b1), y0, (Node (Black, c0,
                     k, r)))))
           | Black -> lbal (Node (Red, a, x, b0)) k r)))

  (** val ins : order -> tree -> tree **)

  let rec ins x s = match s with
  | Leaf -> Node (Red, Leaf, x, Leaf)
  | Node (c, l, y, r) ->
    if Nat.eqb x.id y.id
    then s
    else if Nat.ltb x.id y.id
         then (match c with
               | Red -> Node (Red, (ins x l), y, r)
               | Black -> lbal (ins x l) y r)
         else (match c with
               | Red -> Node (Red, l, y, (ins x r))
               | Black -> rbal l y (ins x r))

  (** val add : order -> tree -> tree **)

  let add x s =
    makeBlack (ins x s)

  (** val append : tree -> tree -> tree **)

  let rec append l = match l with
  | Leaf -> (fun r -> r)
  | Node (lc, ll, lx, lr) ->
    let rec append_l r = match r with
    | Leaf -> l
    | Node (rc, rl, rx, rr) ->
      (match lc with
       | Red ->
         (match rc with
          | Red ->
            let lrl = append lr rl in
            (match lrl with
             | Leaf -> Node (Red, ll, lx, (Node (Red, lrl, rx, rr)))
             | Node (t0, lr', x, rl') ->
               (match t0 with
                | Red ->
                  Node (Red, (Node (Red, ll, lx, lr')), x, (Node (Red, rl',
                    rx, rr)))
                | Black -> Node (Red, ll, lx, (Node (Red, lrl, rx, rr)))))
          | Black -> Node (Red, ll, lx, (append lr r)))
       | Black ->
         (match rc with
          | Red -> Node (Red, (append_l rl), rx, rr)
          | Black ->
            let lrl = append lr rl in
            (match lrl with
             | Leaf -> lbalS ll lx (Node (Black, lrl, rx, rr))
             | Node (t0, lr', x, rl') ->
               (match t0 with
                | Red ->
                  Node (Red, (Node (Black, ll, lx, lr')), x, (Node (Black,
                    rl', rx, rr)))
                | Black -> lbalS ll lx (Node (Black, lrl, rx, rr))))))
    in append_l

  (** val del : order -> tree -> tree **)

  let rec del x = function
  | Leaf -> Leaf
  | Node (_, a, y, b) ->
    if Nat.eqb x.id y.id
    then append a b
    else if Nat.ltb x.id y.id
         then (match a with
               | Leaf -> Node (Red, (del x a), y, b)
               | Node (t1, _, _, _) ->
                 (match t1 with
                  | Red -> Node (Red, (del x a), y, b)
                  | Black -> lbalS (del x a) y b))
         else (match b with
               | Leaf -> Node (Red, a, y, (del x b))
               | Node (t1, _, _, _) ->
                 (match t1 with
                  | Red -> Node (Red, a, y, (del x b))
                  | Black -> rbalS a y (del x b)))

  (** val remove : order -> tree -> tree **)

  let remove x t0 =
    makeBlack (del x t0)
 end

(** val bt : ((((TB.t*TA.t)*T_id.t)*T_id.t)*transaction list) -> TB.t **)

let bt = function
| p0,_ -> let p1,_ = p0 in let p2,_ = p1 in let x,_ = p2 in x

(** val at : ((((TB.t*TA.t)*T_id.t)*T_id.t)*transaction list) -> TA.t **)

let at = function
| p0,_ -> let p1,_ = p0 in let p2,_ = p1 in let _,y = p2 in y

(** val mt :
    ((((TB.t*TA.t)*T_id.t)*T_id.t)*transaction list) -> transaction list **)

let mt = function
| _,z -> z

(** val b_id : ((((TB.t*TA.t)*T_id.t)*T_id.t)*transaction list) -> T_id.t **)

let b_id = function
| p0,_ -> let p1,_ = p0 in let _,x_id = p1 in x_id

(** val a_id : ((((TB.t*TA.t)*T_id.t)*T_id.t)*transaction list) -> T_id.t **)

let a_id = function
| p0,_ -> let _,y_id = p0 in y_id

(** val match_ask :
    TB.t -> TA.t -> TA.elt -> T_id.t -> T_id.t ->
    (((TB.t*TA.t)*T_id.t)*T_id.t)*transaction list **)

let rec match_ask x =
  let o = TB.max_elt x in
  (fun a a0 b_id0 a_id0 ->
  match o with
  | Some e ->
    let n = sub a0.oprice e.oprice in
    ((fun zero succ n -> if n=0 then zero () else succ (n-1))
       (fun _ ->
       let s = lt_eq_lt_dec e.oquantity a0.oquantity in
       (match s with
        | Some s0 ->
          if s0
          then let t0 = TB.remove e x in
               let t_id = T_id.remove e b_id0 in
               let bAM =
                 match_ask t0 a { id = a0.id; otime = a0.otime; oquantity =
                   (sub a0.oquantity e.oquantity); oprice = a0.oprice } t_id
                   a_id0
               in
               ((((bt bAM),(at bAM)),(b_id bAM)),(a_id bAM)),({ idb = e.id;
               ida = a0.id; tquantity = e.oquantity }::(mt bAM))
          else ((((TB.remove e x),a),(T_id.remove e b_id0)),a_id0),({ idb =
                 e.id; ida = a0.id; tquantity = a0.oquantity }::[])
        | None ->
          ((((TB.add { id = e.id; otime = e.otime; oquantity =
               (sub e.oquantity a0.oquantity); oprice = e.oprice }
               (TB.remove e x)),a),(T_id.add { id = e.id; otime = e.otime;
                                     oquantity =
                                     (sub e.oquantity a0.oquantity); oprice =
                                     e.oprice } (T_id.remove e b_id0))),a_id0),({ idb =
            e.id; ida = a0.id; tquantity = a0.oquantity }::[])))
       (fun _ -> (((x,(TA.add a0 a)),b_id0),(T_id.add a0 a_id0)),[])
       n)
  | None -> (((x,(TA.add a0 a)),b_id0),(T_id.add a0 a_id0)),[])

(** val match_bid :
    TB.t -> TA.t -> TA.elt -> T_id.t -> T_id.t ->
    (((TB.t*TA.t)*T_id.t)*T_id.t)*transaction list **)

let rec match_bid b a b0 b_id0 a_id0 =
  let o = TA.max_elt a in
  (match o with
   | Some e ->
     let n = sub e.oprice b0.oprice in
     ((fun zero succ n -> if n=0 then zero () else succ (n-1))
        (fun _ ->
        let s = lt_eq_lt_dec e.oquantity b0.oquantity in
        (match s with
         | Some s0 ->
           if s0
           then let t0 = TA.remove e a in
                let t_id = T_id.remove e a_id0 in
                let bAM =
                  match_bid b t0 { id = b0.id; otime = b0.otime; oquantity =
                    (sub b0.oquantity e.oquantity); oprice = b0.oprice }
                    b_id0 t_id
                in
                ((((bt bAM),(at bAM)),(b_id bAM)),(a_id bAM)),({ idb = b0.id;
                ida = e.id; tquantity = e.oquantity }::(mt bAM))
           else (((b,(TA.remove e a)),b_id0),(T_id.remove e a_id0)),({ idb =
                  b0.id; ida = e.id; tquantity = b0.oquantity }::[])
         | None ->
           (((b,(TA.add { id = e.id; otime = e.otime; oquantity =
                  (sub e.oquantity b0.oquantity); oprice = e.oprice }
                  (TA.remove e a))),b_id0),(T_id.add { id = e.id; otime =
                                             e.otime; oquantity =
                                             (sub e.oquantity b0.oquantity);
                                             oprice = e.oprice }
                                             (T_id.remove e a_id0))),({ idb =
             b0.id; ida = e.id; tquantity = b0.oquantity }::[])))
        (fun _ -> ((((TB.add b0 b),a),(T_id.add b0 b_id0)),a_id0),[])
        n)
   | None -> ((((TB.add b0 b),a),(T_id.add b0 b_id0)),a_id0),[])

(** val search_order : T_id.t -> int -> T_id.elt option **)

let rec search_order t0 i =
  match t0 with
  | T_id.Leaf -> None
  | T_id.Node (_, l, k, r) ->
    (match lt_eq_lt_dec k.id i with
     | Some s -> if s then search_order r i else Some k
     | None -> search_order l i)

(** val del_order :
    TB.t -> TA.t -> int -> T_id.t -> T_id.t ->
    (((TB.t*TA.t)*T_id.t)*T_id.t)*transaction list **)

let del_order b a i b_id0 a_id0 =
  let o = search_order b_id0 i in
  (match o with
   | Some e ->
     let o0 = search_order a_id0 i in
     (match o0 with
      | Some e0 ->
        ((((TB.remove e b),(TA.remove e0 a)),(T_id.remove e b_id0)),(T_id.remove
                                                                    e0 a_id0)),[]
      | None -> ((((TB.remove e b),a),(T_id.remove e b_id0)),a_id0),[])
   | None ->
     let o0 = search_order a_id0 i in
     (match o0 with
      | Some e -> (((b,(TA.remove e a)),b_id0),(T_id.remove e a_id0)),[]
      | None -> (((b,a),b_id0),a_id0),[]))

(** val process_instruction :
    TB.t -> TA.t -> instruction -> T_id.t -> T_id.t ->
    (((TB.t*TA.t)*T_id.t)*T_id.t)*transaction list **)

let process_instruction b a tau b_id0 a_id0 =
  match tau.cmd with
  | Buy -> match_bid b a tau.ord b_id0 a_id0
  | Sell -> match_ask b a tau.ord b_id0 a_id0
  | Del -> del_order b a tau.ord.id b_id0 a_id0

(** val iterate :
    (TB.t -> TA.t -> instruction -> T_id.t -> T_id.t ->
    (((TB.t*TA.t)*T_id.t)*T_id.t)*transaction list) -> instruction list ->
    int -> (((TB.tree*TA.tree)*T_id.tree)*T_id.tree)*transaction list **)

let rec iterate p i k =
  (fun zero succ n -> if n=0 then zero () else succ (n-1))
    (fun _ -> (((TB.empty,TA.empty),T_id.empty),T_id.empty),[])
    (fun k' ->
    let it = iterate p i k' in
    p (bt it) (at it) (nth k' i tau0) (b_id it) (a_id it))
    k

(** val iterated :
    (TB.t -> TA.t -> instruction -> T_id.t -> T_id.t ->
    (((TB.t*TA.t)*T_id.t)*T_id.t)*transaction list) -> instruction list ->
    int -> (((TB.tree*TA.tree)*T_id.tree)*T_id.tree)*transaction list **)

let iterated p i k =
  if Nat.ltb (length i) k
  then (((TB.empty,TA.empty),T_id.empty),T_id.empty),[]
  else iterate p i k

(** val main :
    instruction list -> int -> (((TB.t*TA.t)*T_id.t)*T_id.t)*transaction list **)

let main i k =
  iterated process_instruction i k
