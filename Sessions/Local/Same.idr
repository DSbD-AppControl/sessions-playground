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

notVVElem : (x = y -> Void) -> Local.Call x = Local.Call y -> Void
notVVElem f Refl = f Refl

notVR : Local.Call x = Local.Rec y -> Void
notVR Refl impossible

notVC : Local.Call x = Choice ty whom selections -> Void
notVC Refl impossible

notRRBody : (x = y -> Void) -> Local.Rec x = Local.Rec y -> Void
notRRBody f Refl = f Refl

notRC : Local.Rec x = Choice ty whom selections -> Void
notRC Refl impossible

notCCTy : (tyA = tyB -> Void) -> Local.Choice tyA a as = Local.Choice tyB b bs -> Void
notCCTy f Refl = f Refl

notCCWhom : (a = b -> Void) -> Local.Choice tyA a as = Local.Choice tyA b bs -> Void
notCCWhom f Refl = f Refl

notCCSels : (as = bs -> Void) -> Local.Choice tyA a as = Local.Choice tyA a bs -> Void
notCCSels f Refl = f Refl


mutual

  export
  same : DecEq role label msg
      => (a,b : Local role label msg rs g)
             -> Dec (Equal a b)
  same End End = Yes Refl
  same End (Choice ty whom selections)
    = No (notEC)

  same (Call x) (Call y) with (decEq x y)
    same (Call x) (Call x) | (Yes Refl)
      = Yes Refl
    same (Call x) (Call y) | (No contra)
      = No (notVVElem contra)


  same (Call x) (Rec y)
    = No notVR
  same (Call x) (Choice ty whom selections)
    = No notVC

  same (Rec x) (Call y)
    = No (negEqSym notVR)
  same (Rec x) (Rec y) with (same x y)
    same (Rec x) (Rec x) | (Yes Refl) = Yes Refl
    same (Rec x) (Rec y) | (No contra)
      = No (notRRBody contra)

  same (Rec x) (Choice ty whom selections)
    = No notRC

  same (Choice ty whom selections) End
    = No (negEqSym notEC)
  same (Choice ty whom selections) (Call x)
    = No (negEqSym notVC)
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

    notPairSameLabel : {am, bm : _}
                    -> {ab, bb : _}
                    -> (al = bl -> Void) -> (al, (am, ab)) = (bl, (bm, bb)) -> Void
    notPairSameLabel f Refl = f Refl

    notPairSameMsg : {al : _}
                  -> {ab, bb : _}
                  -> (am = bm -> Void) -> (al, (am, ab)) = (al, (bm, bb)) -> Void
    notPairSameMsg f Refl = f Refl

    notPairSameRest : {al : _}
                   -> {am : _}
                   -> (ab = bb -> Void) -> (al, (am, ab)) = (al, (am, bb)) -> Void
    notPairSameRest f Refl = f Refl

    export
    same : DecEq role label msg
        => (x,y : Branch role label msg rs g)
               -> Dec (Equal x y)
    same (al, (am, ab)) (bl, (bm, bb)) with (decEq al bl)
      same (al, (am, ab)) (al, (bm, bb)) | (Yes Refl) with (decEq am bm)
        same (al, (am, ab)) (al, (am, bb)) | (Yes Refl) | (Yes Refl) with (same ab bb)
          same (al, (am, ab)) (al, (am, ab)) | (Yes Refl) | (Yes Refl) | (Yes Refl)
            = Yes Refl
          same (al, (am, ab)) (al, (am, bb)) | (Yes Refl) | (Yes Refl) | (No contra)
            = No (notPairSameRest contra)
        same (al, (am, ab)) (al, (bm, bb)) | (Yes Refl) | (No contra)
          = No (notPairSameMsg contra)
      same (al, (am, ab)) (bl, (bm, bb)) | (No contra)
        = No (notPairSameLabel contra)

  namespace List

    notSamesRightEmpty : [] = x :: xs -> Void
    notSamesRightEmpty Refl impossible

    notSamesHead : {xs, ys : Branches' roel label msg rs g}
                -> (x = y -> Void)
                -> (::) x xs = (::) y ys
                -> Void
    notSamesHead f Refl = f Refl

    notSamesTail : {xs, ys : Branches' roel label msg rs g}
                -> (xs = ys -> Void)
                -> x :: xs = x :: ys
                -> Void
    notSamesTail f Refl = f Refl

    export
    same : DecEq role label msg
        => (as, bs : Branches' role label msg rs g)
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
    same : DecEq role label msg
        => (as, bs : Branches role label msg rs g)
                  -> Dec (Equal as bs)

    same (a ::: as) (b ::: bs) with (same a b)
      same (a ::: as) (a ::: bs) | (Yes Refl) with (same as bs)
        same (a ::: bs) (a ::: bs) | (Yes Refl) | (Yes Refl)
          = Yes Refl
        same (a ::: as) (a ::: bs) | (Yes Refl) | (No contra)
          = No (notSames1Tail contra)
      same (a ::: as) (b ::: bs) | (No contra)
        = No (notSames1Head contra)


-- [ EOF ]
