||| For Plain Merge we need to compare Local types for equality.
module Sessions.Local.Same

import Decidable.Equality
import Data.List
import Data.List.Elem

import Data.List1

import Sessions.Meta
import Sessions.Local

%default total

notEC : Local.End = Choice ty whom selections -> Void
notEC Refl impossible

notVVElem : (x = y -> Void) -> Local.Var x = Local.Var y -> Void
notVVElem f Refl = f Refl

notVT : Local.Var x = T -> Void
notVT Refl impossible

notVR : Local.Var x = Local.Rec y -> Void
notVR Refl impossible

notVC : Local.Var x = Choice ty whom selections -> Void
notVC Refl impossible

notTR : T = Local.Rec x -> Void
notTR Refl impossible

notRRBody : (x = y -> Void) -> Local.Rec x = Local.Rec y -> Void
notRRBody f Refl = f Refl

notRC : Local.Rec x = Choice ty whom selections -> Void
notRC Refl impossible

notTC : Local.T = Choice ty whom selections -> Void
notTC Refl impossible

notCCTy : (tyA = tyB -> Void) -> Local.Choice tyA a as = Local.Choice tyB b bs -> Void
notCCTy f Refl = f Refl

notCCWhom : (a = b -> Void) -> Local.Choice tyA a as = Local.Choice tyA b bs -> Void
notCCWhom f Refl = f Refl

notCCSels : (as = bs -> Void) -> Local.Choice tyA a as = Local.Choice tyA a bs -> Void
notCCSels f Refl = f Refl


mutual

  export
  same : DecEq role
      => DecEq msg
      => (a,b : Local role msg rs g)
             -> Dec (Equal a b)
  same End End = Yes Refl
  same End (Choice ty whom selections)
    = No (notEC)

  same (Var x) (Var y) with (decEq x y)
    same (Var x) (Var x) | (Yes Refl)
      = Yes Refl
    same (Var x) (Var y) | (No contra)
      = No (notVVElem contra)


  same (Var x) T
    = No (notVT)
  same (Var x) (Rec y)
    = No notVR
  same (Var x) (Choice ty whom selections)
    = No notVC
  same T (Var x)
    = No (negEqSym notVT)

  same T T = Yes Refl
  same T (Rec x)
    = No notTR
  same T (Choice ty whom selections)
    = No notTC

  same (Rec x) (Var y)
    = No (negEqSym notVR)
  same (Rec x) T
    = No (negEqSym notTR)
  same (Rec x) (Rec y) with (same x y)
    same (Rec x) (Rec x) | (Yes Refl) = Yes Refl
    same (Rec x) (Rec y) | (No contra)
      = No (notRRBody contra)

  same (Rec x) (Choice ty whom selections)
    = No notRC

  same (Choice ty whom selections) End
    = No (negEqSym notEC)
  same (Choice ty whom selections) (Var x)
    = No (negEqSym notVC)
  same (Choice ty whom selections) T
    = No (negEqSym notTC)
  same (Choice ty whom selections) (Rec x)
    = No (negEqSym notRC)

  same (Choice tyA a as) (Choice tyB b bs) with (decEq tyA tyB)
    same (Choice tyA a as) (Choice tyA b bs) | (Yes Refl) with (decEq a b)
      same (Choice tyA a as) (Choice tyA a bs) | (Yes Refl) | (Yes Refl) with (List1.same as bs)
        same (Choice tyA a as) (Choice tyA a as) | (Yes Refl) | (Yes Refl) | (Yes Refl)
          = Yes Refl
        same (Choice tyA a as) (Choice tyA a bs) | (Yes Refl) | (Yes Refl) | (No contra)
          = No (notCCSels contra)

      same (Choice tyA a as) (Choice tyA b bs) | (Yes Refl) | (No contra)
        = No (notCCWhom contra)

    same (Choice tyA a as) (Choice tyB b bs) | (No contra)
      = No (notCCTy contra)

  namespace Pair
    notSameBSecond : {ma : msg} -> (la = lb -> Void) -> (ma, la) = (ma, lb) -> Void
    notSameBSecond f Refl = f Refl

    notSameBFirst : {la : _} -> {lb : _} -> (ma = mb -> Void) -> (ma, la) = (mb, lb) -> Void
    notSameBFirst f Refl = f Refl

    export
    same : DecEq role
        => DecEq msg
        => (x,y : Pair msg (Local role msg rs g))
               -> Dec (Equal x y)
    same (ma, la) (mb, lb) with (decEq ma mb)
      same (ma, la) (ma, lb) | (Yes Refl) with (same la lb)
        same (ma, lb) (ma, lb) | (Yes Refl) | (Yes Refl)
          = Yes Refl
        same (ma, la) (ma, lb) | (Yes Refl) | (No contra)
          = No (notSameBSecond contra)
      same (ma, la) (mb, lb) | (No contra)
        = No (notSameBFirst contra)

  namespace List
    notSamesRightEmpty : [] = x :: xs -> Void
    notSamesRightEmpty Refl impossible

    notSamesHead : {xs, ys : List (msg, Local roel msg rs g)} -> (x = y -> Void) -> (::) x xs = (::) y ys -> Void
    notSamesHead f Refl = f Refl

    notSamesTail : {xs, ys : List (msg, Local roel msg rs g)} -> (xs = ys -> Void) -> x :: xs = x :: ys -> Void
    notSamesTail f Refl = f Refl

    export
    same : DecEq role
        => DecEq msg
        => (as, bs : List (msg, Local role msg rs g))
                  -> Dec (Equal as bs)
    same [] [] = Yes Refl
    same [] (x :: xs) = No (notSamesRightEmpty)
    same (x :: xs) [] = No (negEqSym notSamesRightEmpty)
    same (x :: xs) (y :: ys) with (Pair.same x y)
      same (x :: xs) (x :: ys) | (Yes Refl) with (same xs ys)
        same (x :: ys) (x :: ys) | (Yes Refl) | (Yes Refl)
          = Yes Refl
        same (x :: xs) (x :: ys) | (Yes Refl) | (No contra)
          = No (notSamesTail contra)
      same (x :: xs) (y :: ys) | (No contra)
        = No (notSamesHead contra)

  namespace List1
    notSames1Head : (a = b -> Void) -> a ::: as = b ::: bs -> Void
    notSames1Head f Refl = f Refl

    notSames1Tail : (as = bs -> Void) -> a ::: as = a ::: bs -> Void
    notSames1Tail f Refl = f Refl

    export
    same : DecEq role
        => DecEq msg
        => (as, bs : List1 (msg, Local role msg rs g))
                  -> Dec (Equal as bs)
    same (a ::: as) (b ::: bs) with (same a b)
      same (a ::: as) (a ::: bs) | (Yes Refl) with (same as bs)
        same (a ::: bs) (a ::: bs) | (Yes Refl) | (Yes Refl)
          = Yes Refl
        same (a ::: as) (a ::: bs) | (Yes Refl) | (No contra)
          = No (notSames1Tail contra)
      same (a ::: as) (b ::: bs) | (No contra)
        = No (notSames1Head contra)

namespace List
  public export
  data AllSame : (c  : (msg, Local role msg rs g))
              -> (cs : List (msg, Local role msg rs g))
              -> (ne : NonEmpty cs)
                    -> Type
    where
      Base : (prf : Equal c d)
                 -> AllSame c (d :: Nil) IsNonEmpty

      Extend : (prf   : Equal c d)
            -> (prfNE : NonEmpty rest)
            -> (later : AllSame c     rest  prfNE)
                     -> AllSame c (d::rest) IsNonEmpty

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
             -> AllSame c (x :: xs) IsNonEmpty -> Void
  notSameHead f (Base prf) = f prf
  notSameHead f (Extend prf prfNE later) = f prf


  notSameRest : (AllSame x (y :: xs) IsNonEmpty -> Void)
              -> AllSame x (x :: (y :: xs)) IsNonEmpty
              -> Void
  notSameRest f (Extend Refl IsNonEmpty later) = f later

  export
  allSame : DecEq role
         => DecEq msg
         => (c     :      (msg, Local role msg rs g))
         -> (cs    : List (msg, Local role msg rs g))
         -> (prfNE : NonEmpty cs)
                  -> Dec (AllSame c cs prfNE)
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
  data AllSame : (cs : List1 (msg, Local role msg rs g))
              -> Type
    where
      All : AllSame c (c::cs) IsNonEmpty -> AllSame (c ::: cs)

  notAllSame : (AllSame h (h :: t) IsNonEmpty -> Void) -> AllSame (h ::: t) -> Void
  notAllSame f (All x) = f x

  export
  allSame : DecEq role
         => DecEq msg
         => (cs : List1 (msg, Local role msg rs g))
               -> Dec (AllSame cs)
  allSame (head ::: tail) with (allSame head (head :: tail) IsNonEmpty)
    allSame (head ::: tail) | (Yes prf) = Yes (All prf)
    allSame (head ::: tail) | (No contra)
      = No (notAllSame contra)

-- [ EOF ]
