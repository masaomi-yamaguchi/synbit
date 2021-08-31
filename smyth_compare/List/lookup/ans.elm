type Bool
  = True ()
  | False ()

type Nat
  = Z ()
  | S Nat

type List a
  = Nil ()
  | Cons (a, List a)

eq : Nat -> Nat -> Bool
eq m n =
  case m of
     Z () ->
       case n of
          Z () -> True ()
          S nn -> False ()
     S mm ->
       case n of
          Z () -> False ()
          S nn -> eq mm nn

lookupP_ : List (Nat, Nat) -> Nat -> Nat
lookupP_ l v =
  case l of
    Cons p ->
      case eq (#2.2 (#2.1 p)) v of
         True () -> #2.1 (#2.1 p)
         False () -> lookupP_ (#2.2 p) v

lookupP : (List (Nat, Nat), Nat) -> Nat -> (List (Nat, Nat), Nat)
lookupP s v = (#2.1 s, lookupP_ (#2.1 s) v)

specifyFunction2 (lookupP)
  [ (([(1,10), (2,200), (3,33)]<(Nat,Nat)>, 2), 10, ([(1,10), (2,200), (3,33)]<(Nat,Nat)>, 1))
  , (([(1,10), (2,200), (3,33)]<(Nat,Nat)>, 2), 33, ([(1,10), (2,200), (3,33)]<(Nat,Nat)>, 3))
  ]
