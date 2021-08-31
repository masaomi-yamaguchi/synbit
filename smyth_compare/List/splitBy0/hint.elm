type Bool
  = True ()
  | False ()

type Nat
  = Z ()
  | S Nat

type List a
  = Nil ()
  | Cons (a, List a)

append : forall a. List a -> List a -> List a
append <a> l1 l2 =
   case l1 of
     Nil () -> l2
     Cons p -> ??

isLast0 : List Nat -> Bool
isLast0 l =
  case l of
    Nil () -> False ()
    Cons p ->
       case #2.2 p of
          Nil () ->
            case #2.1 p of
              Z () -> True
              S nn -> False
          Cons p2 -> ??

splitBy0P : List Nat -> List (List Nat) -> List Nat
splitBy0P s v =
   case v of
      Nil () ->
        case isLast0 s of
           True () -> Cons<Nat> (Z (), Nil<Nat> ())
           False () -> Nil<Nat> ()
      Cons p -> ??

specifyFunction2 (splitBy0P)
  [ ([1,1,0,2,2,0,3,3]<Nat>, [[1,1]<Nat>, [2,2]<Nat>]<List Nat>, [1,1,2,2]<Nat>)
  , ([1,1]<Nat>, [[1,1]<Nat>, [2,2]<Nat>]<List Nat>, [1,1,2,2]<Nat>)
  , ([1,1,0]<Nat>, [[1,1]<Nat>, [2,2]<Nat>]<List Nat>, [1,1,2,2,0]<Nat>)
  ]

{-
anonymous:~/smyth$ ./smyth forge smyth_compare/List/splitBy0/hint.elm --timeout=600.0
Timed out
-}
