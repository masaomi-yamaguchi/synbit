type Nat
  = Z ()
  | S Nat

type List a
  = Nil ()
  | Cons (a, List a)

type Bool
  = True ()
  | False ()

revAppend : forall a.List a -> List a -> List a
revAppend <a> acc l =
  case l of
    Nil () -> acc
    Cons p -> ??

reverseP : forall a. List a -> List a -> List a
reverseP <a> s v = revAppend<a> (Nil<a>) v


specifyFunction2 (reverseP<Bool>)
  [ ([True, True]<Bool>, [False, True, True]<Bool>, [True, True, False]<Bool>)
  ]

specifyFunction2 (reverseP<Nat>)
  [ ([1,2,3,4]<Nat>, [6,5]<Nat>, [5,6]<Nat>)
  ]

{-
anonymous:~/smyth$ ./smyth forge smyth_compare/List/reverse/hint.elm --timeout=600.0
No solutions.
-}
