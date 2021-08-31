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
                        ret = appendP <a> ((#2.2 ps), (#2.2 s)) (#2.2 pv)
                    in (Cons <a> (#2.1 pv, #2.1 ret), #2.2 ret)

specifyFunction2 (appendP<Nat>)
  [ (([1, 2, 3, 4]<Nat>, [5]<Nat>), [6, 2]<Nat>, ([6, 2]<Nat>, []<Nat>))
  , (([1, 2, 3, 4]<Nat>, [5]<Nat>), [1, 2, 3, 4, 5, 6]<Nat>, ([1, 2, 3, 4]<Nat>, [5, 6]<Nat>))
  ]
