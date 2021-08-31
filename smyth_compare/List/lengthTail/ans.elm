type Nat
  = Z ()
  | S Nat

type List a
  = Nil ()
  | Cons (a, List a)

lengthTailP : List Nat -> Nat -> List Nat
lengthTailP s v =
  case v of
     Z () -> Nil<Nat> ()
     S vv ->
       case s of
          Nil () -> Cons<Nat> (Z (), lengthTailP (Nil<Nat>) vv)
          Cons p -> Cons<Nat> (#2.1 p, lengthTailP (#2.2 p) vv)

specifyFunction2 (lengthTailP)
  [ ([1, 2]<Nat>, 4, [1, 2, 0, 0]<Nat>)
  , ([2, 0]<Nat>, 1, [2]<Nat>)
  ]
