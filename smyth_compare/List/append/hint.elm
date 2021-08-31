type Nat
  = Z ()
  | S Nat

type List a
  = Nil ()
  | Cons (a, List a)

appendP : forall a. (List a, List a) -> List a -> (List a, List a)
appendP <a> s v =
  case v of
    Nil () -> (Nil<a> (), Nil<a> ())
    Cons pv ->
      case #2.1 s of
         Nil () -> (Nil<a> (), Cons<a> pv)
         Cons ps -> let ret : (List a, List a)
                        ret = ??
                    in ??

specifyFunction2 (appendP<Nat>)
  [ (([1, 2, 3, 4]<Nat>, [5]<Nat>), [6, 2]<Nat>, ([6, 2]<Nat>, []<Nat>))
  , (([1, 2, 3, 4]<Nat>, [5]<Nat>), [1, 2, 3, 4, 5, 6]<Nat>, ([1, 2, 3, 4]<Nat>, [5, 6]<Nat>))
  ]

{-
anonymous:~/smyth$ ./smyth forge smyth_compare/List/append/hint.elm --timeout=600.0
No solutions.
-}
