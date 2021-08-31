type Nat
  = Z ()
  | S Nat

type List a
  = Nil ()
  | Cons (a, List a)

lengthP : List Nat -> Nat -> List Nat
lengthP s v =
  case v of
     Z () -> Nil<Nat> ()
     S vv ->
       case s of
          Nil () -> Cons<Nat> (Z (), lengthP (Nil<Nat>) vv)
          Cons p -> Cons<Nat> (#2.1 p, lengthP (#2.2 p) vv)

specifyFunction2 (lengthP)
  [ ([1, 2]<Nat>, 4, [1, 2, 0, 0]<Nat>)
  , ([2, 0]<Nat>, 1, [2]<Nat>)
  ]
