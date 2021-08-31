type Nat
  = Z ()
  | S Nat

type PS
 = Professor Nat
 | Student Nat

type List a
  = Nil ()
  | Cons (a, List a)

professorP : List PS -> List Nat -> List PS
professorP s v =
   case s of
      Nil () ->
         case v of
             Nil () -> Nil<PS> ()
             Cons pv -> ??
      Cons ps ->
         case (#2.1 ps) of
             Professor ids ->
                case v of
                   Nil () -> ??
                   Cons pv -> ??
             Student ids -> ??

specifyFunction2 (professorP)
  [ ([Student 11, Student 12, Professor 21, Student 13, Professor 22]<PS>,[31,32,33]<Nat>,[Student 11, Student 12, Professor 31, Student 13, Professor 32, Professor 33]<PS>)
  , ([Student 11, Student 12, Professor 21, Student 13, Professor 22]<PS>,[31]<Nat>,[Student 11, Student 12, Professor 31, Student 13]<PS>)
  , ([Student 11, Student 12, Professor 21, Student 13, Professor 22]<PS>,[31,32,33,34]<Nat>,[Student 11, Student 12, Professor 31, Student 13, Professor 32, Professor 33, Professor 34]<PS>) -- added
  ]

{-
anonymous:~/smyth$ ./smyth forge smyth_compare/List/professor/hint.elm --timeout=600.0
No solutions.
-}
