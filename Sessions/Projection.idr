module Sessions.Projection

import Decidable.Equality
import Data.List
import Data.List.Elem

import Data.List1

import Sessions.Meta

import Sessions.Global
import Sessions.Global.Involved

import Sessions.Local
import Sessions.Local.Same
import Sessions.Local.Same.All

import public Sessions.Projection.Error

%hide Data.List.merge

%default total

mutual

  namespace Term
    public export
    data Project : (tyHowMerge : {rs : List Ty}
                              -> {g  :      Ty}
                              -> (this  : List1 (typeL, typeM, Local typeR typeL typeM rs g))
                              -> (that  :                      Local typeR typeL typeM rs g)
                                       -> Type)
                -> (role  : typeR)
                -> (termG : Global typeR typeL typeM rs g)
                -> (termL : Local  typeR typeL typeM rs g)
                        -> Type
      where
        End : {merge : {rs    : List Ty}
                    -> {g     :      Ty}
                    -> (this  : List1 (typeL, typeM, Local typeR typeL typeM rs g))
                    -> (that  :                      Local typeR typeL typeM rs g)
                             -> Type}
                    -> Project merge whom End End

        Call : {merge : {rs    : List Ty}
                     -> {g     :      Ty}
                     -> (this  : List1 (typeL, typeM, Local typeR typeL typeM rs g))
                     -> (that  :                      Local typeR typeL typeM rs g)
                              -> Type}
                     -> Project merge whom (Call idx) (Call idx)

        Rec : {merge : {rs    : List Ty}
                    -> {g     :      Ty}
                    -> (this  : List1 (typeL, typeM, Local typeR typeL typeM rs g))
                    -> (that  :                      Local typeR typeL typeM rs g)
                             -> Type}
            -> (rec : Term.Project merge whom      x       y)
                   -> Term.Project merge whom (Rec x) (Rec y)

        ChoiceSelect : {merge : {rs    : List Ty}
                             -> {g     :      Ty}
                             -> (this  : List1 (typeL, typeM, Local typeR typeL typeM rs g))
                             -> (that  :                      Local typeR typeL typeM rs g)
                                      -> Type}
                    -> (prfS : whom = s)
                    -> (ss   : List1.Project merge whom bs cs)

                            -> Project merge whom (Choice        s r notsr bs)
                                                  (Choice SELECT   r       cs)

        ChoiceBranch : {merge : {rs    : List Ty}
                             -> {g     :      Ty}
                             -> (this  : List1 (typeL, typeM, Local typeR typeL typeM rs g))
                             -> (that  :                      Local typeR typeL typeM rs g)
                                      -> Type}
                    -> (prfR : whom = r)
                    -> (cs   : List1.Project merge whom bs bs')
                            -> Term.Project  merge whom (Choice        s r notsr bs)
                                                        (Choice BRANCH s         bs')


        ChoiceMerge : {merge : {rs    : List Ty}
                            -> {g     :      Ty}
                            -> (this  : List1 (typeL, typeM, Local typeR typeL typeM rs g))
                            -> (that  :                      Local typeR typeL typeM rs g)
                                     -> Type}
                   -> (prfWS : Not (whom = s))
                   -> (prfWR : Not (whom = r))

                   -> (ss    : List1.Project merge whom bs ((cl,cm,c):::cs))

                   -> (prf   : merge ((cl,cm,c):::cs) d)
                            -> Project merge whom (Choice s r notsr bs)
                                                  d

  namespace List

    public export
    data Project : (tyHowMerge : {rs    : List Ty}
                              -> {g     :      Ty}
                              -> (this  : List1 (typeL, typeM, Local typeR typeL typeM rs g))
                              -> (that  :                      Local typeR typeL typeM rs g)
                                       -> Type)
                -> (role : typeR)
                -> (bs   : List (typeL, typeM, Global typeR typeL typeM rs g))
                -> (bs'  : List (typeL, typeM, Local  typeR typeL typeM rs g))
                        -> Type
      where
        Empty : {merge : {rs    : List Ty}
                      -> {g     :      Ty}
                      -> (this  : List1 (typeL, typeM, Local typeR typeL typeM rs g))
                      -> (that  :                      Local typeR typeL typeM rs g)
                               -> Type}
                      -> Project merge whom Nil Nil

        Ext : {merge : {rs    : List Ty}
                    -> {g     :      Ty}
                    -> (this  : List1 (typeL, typeM, Local typeR typeL typeM rs g))
                    -> (that  :                      Local typeR typeL typeM rs g)
                             -> Type}
           -> (this : Term.Project merge whom         x               y)
           -> (rest : List.Project merge whom             xs              ys)
                   -> List.Project merge whom ((xl,xm,x)::xs) ((xl,xm,y)::ys)

  namespace List1

    public export
    data Project : (tyHowMerge : {rs : List Ty}
                              -> {g  :      Ty}
                              -> (this  : List1 (typeL, typeM, Local typeR typeL typeM rs g))
                              -> (that  :                      Local typeR typeL typeM rs g)
                                       -> Type)
                -> (role : typeR)
                -> (bs   : List1 (typeL, typeM, Global typeR typeL typeM rs g))
                -> (bs'  : List1 (typeL, typeM, Local  typeR typeL typeM rs g))
                        -> Type
      where
        Proj : {merge : {rs    : List Ty}
                    -> {g     :      Ty}
                    -> (this  : List1 (typeL, typeM, Local typeR typeL typeM rs g))
                    -> (that  :                      Local typeR typeL typeM rs g)
                             -> Type}
            -> (what  : List.Project  merge whom (b ::bs) (c ::cs))
                     -> List1.Project merge whom (b:::bs) (c:::cs)

mutual
  namespace Term

    public export
    project : DecEq typeR typeL typeM
           => {mergeTy : {rs    : List Ty}
                      -> {g     :      Ty}
                      -> (this  : List1 (typeL, typeM, Local typeR typeL typeM rs g))
                      -> (that  :                      Local typeR typeL typeM rs g)
                               -> Type}
           -> (mergeOp : {rs   : List Ty}
                      -> {g    :      Ty}
                      -> (this : List1 (typeL, typeM, Local typeR typeL typeM rs g))
                              -> Maybe (that ** mergeTy this that))
           -> {rs    : List Ty}
           -> {g     :      Ty}
           -> (role  : typeR)
           -> (termG : Global typeR typeL typeM rs g)
                    -> Maybe (termL ** Project mergeTy role termG termL)

    project _ _ End
      = Just (End ** End)

    project _ _ (Call x)
      = Just (Call x ** Call)

    project mergeOp role (Rec x)
      = do (x' ** prf) <- project mergeOp role x
           pure (Rec x' ** Rec prf)

    project mergeOp role (Choice s r notSR cs) with (involved role s r notSR)
      project mergeOp role (Choice role r notSR cs) | (Sends Refl)
        = do (cs' ** prf) <- project mergeOp role cs
             pure (Choice SELECT r cs' ** ChoiceSelect Refl prf)

      project mergeOp role (Choice s role notSR cs) | (Recvs Refl)
        = do (cs' ** prf) <- project mergeOp role cs
             pure (Choice BRANCH s cs' ** ChoiceBranch Refl prf)

      project mergeOp role (Choice s r notSR cs) | (Skips prfSNot prfRNot)
        = do ((l,(m,c')) ::: tail ** prfProj) <- project mergeOp role cs
             (c ** prfMerge) <- mergeOp ((l,(m,c')) ::: tail)
             pure (c ** ChoiceMerge prfSNot prfRNot prfProj prfMerge)

  namespace List

    public export
    project : DecEq typeR typeL typeM
           => {mergeTy : {rs    : List Ty}
                      -> {g     :      Ty}
                      -> (this  : List1 (typeL, typeM, Local typeR typeL typeM rs g))
                      -> (that  :                      Local typeR typeL typeM rs g)
                               -> Type}
           -> (mergeOp : {rs   : List Ty}
                      -> {g    :      Ty}
                      -> (this : List1 (typeL, typeM, Local typeR typeL typeM rs g))
                              -> Maybe (that ** mergeTy this that))

           -> {rs   : List Ty}
           -> {g    :      Ty}
           -> (role : typeR)
           -> (bs   : List (typeL, typeM, Global typeR typeL typeM rs g))
                   -> Maybe (bs' ** List.Project mergeTy role bs bs')

    project _ _ []
      = pure (Nil ** Empty)

    project mergeOp role ((l,(m,x)) :: xs)

      = do (x'  ** prfX)  <- Term.project mergeOp role x
           (xs' ** prfXs) <- List.project mergeOp role xs

           pure ((l,(m,x')) :: xs' ** Ext prfX prfXs)

  namespace List1

    public export
    project : DecEq typeR typeL typeM
           => {mergeTy : {rs    : List Ty}
                      -> {g     :      Ty}
                      -> (this  : List1 (typeL, typeM, Local typeR typeL typeM rs g))
                      -> (that  :                      Local typeR typeL typeM rs g)
                               -> Type}
           -> (mergeOp : {rs   : List Ty}
                      -> {g    :      Ty}
                      -> (this : List1 (typeL, typeM, Local typeR typeL typeM rs g))
                              -> Maybe (that ** mergeTy this that))

           -> {rs    : List Ty}
           -> {g     :      Ty}
           -> (role  : typeR)
           -> (termG : List1 (typeL, typeM, Global typeR typeL typeM rs g))
                    -> Maybe (termL ** Project mergeTy role termG termL)

    project mergeOp role (head ::: tail)
      = do (x::xs ** prf) <- List.project mergeOp role (head::tail)
           pure (x:::xs ** Proj prf)

-- [ EOF ]
