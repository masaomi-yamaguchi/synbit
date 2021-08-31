type Nat
  = Z ()
  | S Nat

type List a
  = Nil ()
  | Cons (a, List a)

type Bool
  = True ()
  | False ()

length : forall a. List a -> Nat
length <a> l =
  case l of
     Nil () -> Z ()
     Cons p -> ??

head : forall a. List a -> a
head <a> l =
   case l of
      Cons p -> ??

replicateP : forall a. (a, Nat) -> List a -> (a, Nat)
replicateP <a> s v = (head <a> v, length <a> v)

specifyFunction2 (replicateP<Nat>) -- type is different, but it is not important
  [ ((0, 2), [0,0,0]<Nat>, (0, 3))]

specifyFunction2 (replicateP<Bool>)
  [ ((True, 3), [False,False]<Bool>, (False, 2))]

{-
anonymous:~/smyth$ ./smyth forge smyth_compare/Nat/uncurryReplicate/hint.elm --timeout=600.0
??0:

S (length <a> (#2.2 p))

??1:

#2.1 p
-}
