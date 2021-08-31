type Nat
  = Z ()
  | S Nat

addP : (Nat,Nat) -> Nat -> (Nat,Nat)
addP s v =
  case #2.1 s of
    Z () -> (Z (), v)
    S s1 ->
      case v of
         Z () -> (Z (), Z ())
         S vv -> let a : (Nat,Nat)
                     a = addP (s1, #2.2 s) vv
                 in (S (#2.1 a), #2.2 a)

specifyFunction2 addP
  [ ((2,3), 7, (2,5))
  , ((2,3), 1, (1,0))
  ]
