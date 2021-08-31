type List a
  = Nil ()
  | Cons (a, List a)

type Bool
  = True ()
  | False ()

not : Bool -> Bool
not b =
  case b of
    True _ ->
      False ()

    False _ ->
      True ()

go : List Bool -> List Bool
go l =
  case l of
    Nil _ -> Nil<Bool> ()
    Cons p ->
      case #2.1 p of
          True _ -> Cons <Bool> (False (), go (#2.2 p))
          False _ -> Cons <Bool> (True (), go (#2.2 p))

mapNotP : List Bool -> List Bool -> List Bool
mapNotP s v = go v

specifyFunction2 mapNotP
  [ ([True, False]<Bool>, [True, True, False]<Bool>, [False, False, True]<Bool>)
  , ([True, False]<Bool>, [True, True, False,True]<Bool>, [False, False, True,False]<Bool>)
  , ([False,True]<Bool>, [False]<Bool>, [True]<Bool>)
  ]
