
(** val sub : int -> int -> int **)

let rec sub = fun n m -> if m>n then 0 else n-m

module Nat =
 struct
  (** val eqb : int -> int -> bool **)

  let rec eqb = ( = )

  (** val leb : int -> int -> bool **)

  let rec leb = (<=)

  (** val ltb : int -> int -> bool **)

  let ltb = (<)
 end

type color =
| Red
| Black

module Color =
 struct
  type t = color
 end

(** val lt_eq_lt_dec : int -> int -> bool option **)

let rec lt_eq_lt_dec = fun n m -> if n>m then None else Some (n<m)

type order = { id : int; otime : int; oquantity : int; oprice : int }

type transaction = { idb : int; ida : int; tquantity : int }

type command =
| Buy
| Sell
| Del

type instruction = { cmd : command; ord : order }

(** val pr1 : ('a1 * 'a2) -> 'a1 **)

let pr1 = function
| pr3,_ -> pr3

(** val pr2 : ('a1 * 'a2) -> 'a2 **)

let pr2 = function
| _,pr3 -> pr3

module TB =
 struct
  type elt = order

  type tree =
  | Leaf
  | Node of Color.t * tree * order * tree

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

(** val bt_id : ((((TB.t*TA.t)*T_id.t)*T_id.t)*transaction list) -> T_id.t **)

let bt_id = function
| p0,_ -> let p1,_ = p0 in let _,x_id = p1 in x_id

(** val at_id : ((((TB.t*TA.t)*T_id.t)*T_id.t)*transaction list) -> T_id.t **)

let at_id = function
| p0,_ -> let _,y_id = p0 in y_id

(** val eMatch_ask :
    TB.t -> TA.t -> TA.elt -> T_id.t -> T_id.t ->
    (((TB.t*TA.t)*T_id.t)*T_id.t)*transaction list **)

let eMatch_ask a a0 a1 a2 b =
  let rec fix_F x =
    let b0 = pr1 x in
    let a3 = pr1 (pr2 (pr2 x)) in
    (match TB.max_elt b0 with
     | Some e ->
       if Nat.eqb (sub a3.oprice e.oprice) 0
       then (match lt_eq_lt_dec e.oquantity a3.oquantity with
             | Some s ->
               if s
               then let b1 = TB.remove e b0 in
                    let b0_id = T_id.remove e (pr1 (pr2 (pr2 (pr2 x)))) in
                    let bAM =
                      let y = b1,((pr1 (pr2 x)),({ id = a3.id; otime =
                        a3.otime; oquantity = (sub a3.oquantity e.oquantity);
                        oprice =
                        a3.oprice },(b0_id,(pr2 (pr2 (pr2 (pr2 x)))))))
                      in
                      fix_F y
                    in
                    ((((bt bAM),(at bAM)),(bt_id bAM)),(at_id bAM)),({ idb =
                    e.id; ida = a3.id; tquantity = e.oquantity }::(mt bAM))
               else ((((TB.remove e b0),(pr1 (pr2 x))),(T_id.remove e
                                                         (pr1
                                                           (pr2 (pr2 (pr2 x)))))),
                      (pr2 (pr2 (pr2 (pr2 x))))),({ idb = e.id; ida = a3.id;
                      tquantity = a3.oquantity }::[])
             | None ->
               ((((TB.add { id = e.id; otime = e.otime; oquantity =
                    (sub e.oquantity a3.oquantity); oprice = e.oprice }
                    (TB.remove e b0)),(pr1 (pr2 x))),(T_id.add { id = e.id;
                                                       otime = e.otime;
                                                       oquantity =
                                                       (sub e.oquantity
                                                         a3.oquantity);
                                                       oprice = e.oprice }
                                                       (T_id.remove e
                                                         (pr1
                                                           (pr2 (pr2 (pr2 x))))))),
                 (pr2 (pr2 (pr2 (pr2 x))))),({ idb = e.id; ida = a3.id;
                 tquantity = a3.oquantity }::[]))
       else (((b0,(TA.add a3 (pr1 (pr2 x)))),(pr1 (pr2 (pr2 (pr2 x))))),
              (T_id.add a3 (pr2 (pr2 (pr2 (pr2 x)))))),[]
     | None ->
       (((TB.Leaf,(TA.add a3 (pr1 (pr2 x)))),(pr1 (pr2 (pr2 (pr2 x))))),
         (T_id.add a3 (pr2 (pr2 (pr2 (pr2 x)))))),[])
  in fix_F (a,(a0,(a1,(a2,b))))

(** val eMatch_bid :
    TB.t -> TA.t -> TA.elt -> T_id.t -> T_id.t ->
    (((TB.t*TA.t)*T_id.t)*T_id.t)*transaction list **)

let eMatch_bid a a0 a1 a2 b =
  let rec fix_F x =
    let a3 = pr1 (pr2 x) in
    let b0 = pr1 (pr2 (pr2 x)) in
    (match TA.max_elt a3 with
     | Some e ->
       if Nat.eqb (sub e.oprice b0.oprice) 0
       then (match lt_eq_lt_dec b0.oquantity e.oquantity with
             | Some s ->
               if s
               then ((((pr1 x),(TA.add { id = e.id; otime = e.otime;
                                 oquantity = (sub e.oquantity b0.oquantity);
                                 oprice = e.oprice } (TA.remove e a3))),
                      (pr1 (pr2 (pr2 (pr2 x))))),(T_id.add { id = e.id;
                                                   otime = e.otime;
                                                   oquantity =
                                                   (sub e.oquantity
                                                     b0.oquantity); oprice =
                                                   e.oprice }
                                                   (T_id.remove e
                                                     (pr2 (pr2 (pr2 (pr2 x))))))),({ idb =
                      b0.id; ida = e.id; tquantity = b0.oquantity }::[])
               else ((((pr1 x),(TA.remove e a3)),(pr1 (pr2 (pr2 (pr2 x))))),
                      (T_id.remove e (pr2 (pr2 (pr2 (pr2 x)))))),({ idb =
                      b0.id; ida = e.id; tquantity = b0.oquantity }::[])
             | None ->
               let a4 = TA.remove e a3 in
               let a0_id = T_id.remove e (pr2 (pr2 (pr2 (pr2 x)))) in
               let bAM =
                 let y = (pr1 x),(a4,({ id = b0.id; otime = b0.otime;
                   oquantity = (sub b0.oquantity e.oquantity); oprice =
                   b0.oprice },((pr1 (pr2 (pr2 (pr2 x)))),a0_id)))
                 in
                 fix_F y
               in
               ((((bt bAM),(at bAM)),(bt_id bAM)),(at_id bAM)),({ idb =
               b0.id; ida = e.id; tquantity = e.oquantity }::(mt bAM)))
       else ((((TB.add b0 (pr1 x)),a3),(T_id.add b0 (pr1 (pr2 (pr2 (pr2 x)))))),
              (pr2 (pr2 (pr2 (pr2 x))))),[]
     | None ->
       ((((TB.add b0 (pr1 x)),TA.Leaf),(T_id.add b0 (pr1 (pr2 (pr2 (pr2 x)))))),
         (pr2 (pr2 (pr2 (pr2 x))))),[])
  in fix_F (a,(a0,(a1,(a2,b))))

(** val search_order : T_id.t -> int -> T_id.elt option **)

let rec search_order t0 i =
  match t0 with
  | T_id.Leaf -> None
  | T_id.Node (_, l, k, r) ->
    (match lt_eq_lt_dec k.id i with
     | Some s -> if s then search_order r i else Some k
     | None -> search_order l i)

(** val eDel_order :
    TB.t -> TA.t -> int -> T_id.t -> T_id.t ->
    (((TB.t*TA.t)*T_id.t)*T_id.t)*transaction list **)

let eDel_order b a i b_id a_id =
  let o = search_order b_id i in
  (match o with
   | Some e ->
     let o0 = search_order a_id i in
     (match o0 with
      | Some e0 ->
        ((((TB.remove e b),(TA.remove e0 a)),(T_id.remove e b_id)),(T_id.remove
                                                                    e0 a_id)),[]
      | None -> ((((TB.remove e b),a),(T_id.remove e b_id)),a_id),[])
   | None ->
     let o0 = search_order a_id i in
     (match o0 with
      | Some e -> (((b,(TA.remove e a)),b_id),(T_id.remove e a_id)),[]
      | None -> (((b,a),b_id),a_id),[]))

(** val eProcess_instruction :
    TB.t -> TA.t -> instruction -> T_id.t -> T_id.t ->
    (((TB.t*TA.t)*T_id.t)*T_id.t)*transaction list **)

let eProcess_instruction b a tau b_id a_id =
  match tau.cmd with
  | Buy -> eMatch_bid b a tau.ord b_id a_id
  | Sell -> eMatch_ask b a tau.ord b_id a_id
  | Del -> eDel_order b a tau.ord.id b_id a_id
