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
                     a = ??
                 in ??

specifyFunction2 addP
  [ ((2,3), 7, (2,5))
  , ((2,3), 1, (1,0))
  , ((3,3), 4, (3,1)) -- added
  ]

{-
anonymous:~/smyth$ ./smyth forge smyth_compare/Nat/add/hint.elm --timeout=600.0
No solutions.
-}
