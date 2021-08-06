||| For Plain Merge we need to assert that all branches in a choice are the same.
module Sessions.Local.Same.All

import Decidable.Equality
import Data.List
import Data.List.Elem

import Data.List1

import Sessions.Meta
import Sessions.Local
import Sessions.Local.Same

%default total


namespace List
  public export
  data All : (c  : Branch    role local msg rs g)
          -> (cs : Branches' role local msg rs g)
          -> (ne : NonEmpty cs)
                -> Type
    where
      Base : (prf : Equal c d)
                 -> All c (d :: Nil) IsNonEmpty

      Extend : (prf   : Equal c d)
            -> (prfNE : NonEmpty rest)
            -> (later : All c     rest  prfNE)
                     -> All c (d::rest) IsNonEmpty

  notEmpty : NonEmpty [] -> Void
  notEmpty IsNonEmpty impossible

  nonEmpty : (xs : List a) -> Dec (NonEmpty xs)
  nonEmpty [] = No notEmpty
  nonEmpty (x :: xs) = Yes IsNonEmpty

  data Shape : (xs : List a) -> Type where
    IsCons : Shape (x::xs)
    IsNil  : Shape Nil

  shape : (xs : List a) -> Shape xs
  shape [] = IsNil
  shape (x :: xs) = IsCons

  notSameHead : (c = x -> Void)
             -> All c (x :: xs) IsNonEmpty -> Void
  notSameHead f (Base prf) = f prf
  notSameHead f (Extend prf prfNE later) = f prf


  notSameRest : (All x (y :: xs) IsNonEmpty -> Void)
              -> All x (x :: (y :: xs)) IsNonEmpty
              -> Void
  notSameRest f (Extend Refl IsNonEmpty later) = f later

  export
  allSame : DecEq role label msg
         => (c     : Branch    role label msg rs g)
         -> (cs    : Branches' role label msg rs g)
         -> (prfNE : NonEmpty cs)
                  -> Dec (All c cs prfNE)
  allSame c (x :: xs) IsNonEmpty with (same c x)
    allSame x (x :: xs) IsNonEmpty | (Yes Refl) with (shape xs)
      allSame x (x :: (y :: xs)) IsNonEmpty | (Yes Refl) | IsCons with (allSame x (y::xs) IsNonEmpty)
        allSame x (x :: (y :: xs)) IsNonEmpty | (Yes Refl) | IsCons | (Yes prf) = Yes (Extend Refl IsNonEmpty prf)
        allSame x (x :: (y :: xs)) IsNonEmpty | (Yes Refl) | IsCons | (No contra)
          = No (notSameRest contra)
      allSame x (x :: []) IsNonEmpty | (Yes Refl) | IsNil
        = Yes (Base Refl)

    allSame c (x :: xs) IsNonEmpty | (No contra)
      = No (notSameHead contra)

namespace List1
  public export
  data All : (cs : Branches role label msg rs g)
              -> Type
    where
      Yes : All c (c::cs) IsNonEmpty -> All (c ::: cs)

  notAllSame : (All h (h :: t) IsNonEmpty -> Void) -> All (h ::: t) -> Void
  notAllSame f (Yes x) = f x

  export
  allSame : DecEq role label msg
         => (cs : Branches role label msg rs g)
               -> Dec (All cs)
  allSame (head ::: tail) with (allSame head (head :: tail) IsNonEmpty)
    allSame (head ::: tail) | (Yes prf) = Yes (Yes prf)
    allSame (head ::: tail) | (No contra)
      = No (notAllSame contra)

-- [ EOF ]
