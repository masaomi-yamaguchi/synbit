type List a
  = Nil ()
  | Cons (a, List a)

type Nat
  = Z ()
  | S Nat

length : forall a. List a -> Nat
length <a> l =
  case l of
     Nil () -> Z ()
     Cons p -> ??

head : forall a. List a -> a
head <a> l =
   case l of
      Cons p -> ??

go : forall a. List (List a) -> List (a, Nat)
go <a> l =
  case l of
    Nil () -> Nil<(a,Nat)> ()
    Cons p -> ??

mapReplicateP : forall a. List (a, Nat) -> List (List a) -> List (a, Nat)
mapReplicateP <a> s v = go <a> v

specifyFunction2 (mapReplicateP<Nat>)
  [ ([(2,2)]<(Nat,Nat)>, [[1,1,1]<Nat>, [2]<Nat>, [3,3]<Nat>]<List Nat>, [(1,3),(2,1),(3,2)]<(Nat,Nat)>)
  , ([(1,3),(2,1),(3,2)]<(Nat,Nat)>, [[2,2]<Nat>]<List Nat>, [(2,2)]<(Nat,Nat)>)
  ]

{-
anonymous:~/smyth$ ./smyth forge smyth_compare/List/mapReplicate/hint.elm --timeout=600.0
??0:

S (length <a> (#2.2 p))

??1:

#2.1 p

??2:

Cons<(a, Nat)>
  ( ( head <a> (#2.1 p)
    , length <a> (#2.1 p)
    )
  , go <a> (#2.2 p)
  )
-}
