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
        Nil () -> Cons<(Nat,Nat)> ((#2.1 pv,Z ()), mapFstP (Nil<(Nat,Nat)>) (#2.2 pv))
        Cons ps -> Cons<(Nat,Nat)> ((#2.1 pv, #2.2 (#2.1 ps)), mapFstP (#2.2 ps) (#2.2 pv))


specifyFunction2 (mapFstP)
  [ ([(1,10), (2,22), (3, 13)]<(Nat,Nat)>, [1,3]<Nat>, [(1,10), (3, 22)]<(Nat,Nat)>)
  , ([(2,22), (3, 13)]<(Nat,Nat)>, [0,1,2,3]<Nat>, [(0,22), (1,13), (2,0), (3,0)]<(Nat,Nat)>)
  ]
