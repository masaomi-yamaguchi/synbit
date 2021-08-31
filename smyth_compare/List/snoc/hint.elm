type Nat
  = Z ()
  | S Nat

type List a
  = Nil ()
  | Cons (a, List a)

go : forall a. List a -> (List a, a)
go <a> l =
   case l of
     Cons p ->
       case #2.2 p of
          Nil () -> (Nil<a>, #2.1 p)
          Cons pp ->
             let a : (List a, a)
                 a = ??
             in ??

snocP : forall a. (List a, a) -> List a -> (List a, a)
snocP <a> s v = go <a> v

specifyFunction2 (snocP<Nat>)
  [ (([1, 2, 3]<Nat>, 4), [1, 2, 3]<Nat>, ([1, 2]<Nat>, 3))
  , (([1, 2, 3]<Nat>, 4), [1, 2, 3, 4, 5, 6]<Nat>, ([1, 2, 3, 4, 5]<Nat>, 6))
  ]

{-
anonymous:~/smyth$ ./smyth forge smyth_compare/List/snoc/hint.elm --timeout=600.0
No solutions.
-}
