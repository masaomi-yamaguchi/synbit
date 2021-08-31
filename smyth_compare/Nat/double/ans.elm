type Nat
  = Z ()
  | S Nat


doubleP_ : Nat -> Nat
doubleP_ y =
  case y of
    Z () -> Z ()
    S (y2) ->
       case y2 of
          S (y3) -> S (doubleP_ y3)

doubleP : Nat -> Nat -> Nat
doubleP x y = doubleP_ y

specifyFunction2 doubleP
  [ (1, 6, 3)
  , (5, 4, 2)
  ]
