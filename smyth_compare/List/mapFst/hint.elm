type List a
  = Nil ()
  | Cons (a, List a)

type Nat
  = Z ()
  | S Nat

mapFstP : List (Nat, Nat) -> List Nat -> List (Nat, Nat)
mapFstP s v =
  case v of
    Nil () -> Nil<(Nat,Nat)> ()
    Cons pv ->
      case s of
        Nil () -> ??
        Cons ps -> ??


specifyFunction2 (mapFstP)
  [ ([(1,10), (2,22), (3, 13)]<(Nat,Nat)>, [1,3]<Nat>, [(1,10), (3, 22)]<(Nat,Nat)>)
  , ([(2,22), (3, 13)]<(Nat,Nat)>, [0,1,2,3]<Nat>, [(0,22), (1,13), (2,0), (3,0)]<(Nat,Nat)>)
  ]

{-
anonymous:~/smyth$ ./smyth forge smyth_compare/List/mapFst/hint.elm --timeout=600.0
No solutions.
-}
