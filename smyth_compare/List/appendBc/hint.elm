type Bool
  = True ()
  | False ()

type Nat
  = Z ()
  | S Nat

type List a
  = Nil ()
  | Cons (a, List a)

eqN : Nat -> Nat -> Bool
eqN m n =
  case m of
     Z () ->
       case n of
          Z () -> True ()
          S nn -> False ()
     S mm ->
       case n of
          Z () -> False ()
          S nn -> ??

eq : List Nat -> List Nat -> Bool
eq a b =
  case a of
    Nil () ->
      case b of
         Nil () -> True ()
         Cons _ -> False ()
    Cons pa ->
       case b of
         Nil _ -> True ()
         Cons pb ->
            case eqN (#2.1 pa) (#2.1 pb) of
               False () -> False ()
               True () -> ??

go : List Nat -> List Nat -> List Nat
go v d =
  case eq v d of
    True () -> Nil <Nat> ()
    False () ->
        case v of
          Cons pv -> ??

appendBcP : List Nat -> List Nat -> List Nat
appendBcP s v = go v ([0,0]<Nat>)

specifyFunction2 (appendBcP)
  [ ([1,2]<Nat>, [1,0,0]<Nat>, [1]<Nat>),
    ([1,2]<Nat>, [1,2,3,0,0]<Nat>, [1,2,3]<Nat>)
  ]

{-
anonymous:~/smyth$ ./smyth forge smyth_compare/List/appendBc/hint.elm --timeout=600.0
No solutions.
-}
