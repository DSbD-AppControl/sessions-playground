||| Projection based on Plain Merge.
|||
||| The POPL '08 Paper /Multi-Party Asynchronous Session Types/.
||| When projecting a =Choice= in which the projected role is not involved,
||| projection occurs when all choices are equal.
module Sessions.Projection.Plain

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

%default total


mutual

  namespace Term
    public export
    data Project : (role  : typeR)
                -> (termG : Global typeR typeL typeM rs g)
                -> (termL : Local  typeR typeL typeM rs g)
                        -> Type
      where
        End : Project whom End End

        Var : Project whom (Var idx) (Var idx)

        T   : Project whom T T

        Rec : Project whom x y
           -> Project whom (Rec x) (Rec y)

        ChoiceSelect : (prfS : whom = s)
                    -> (ss   : List1.Project whom bs cs)

                            -> Project whom (Choice        s r notsr bs)
                                            (Choice SELECT   r       cs)

        ChoiceBranch : (prfR : whom = r)
                    -> (cs   : List1.Project whom bs bs')
                            -> Project whom (Choice        s r notsr bs)
                                            (Choice BRANCH s         bs')


        ChoiceMerge : (prfWS : Not (whom = s))
                   -> (prfWR : Not (whom = r))

                   -> (ss    : List1.Project whom bs ((cl,cm,c):::cs))
                   -> (prf   : All ((cl,cm,c):::cs))

                            -> Project whom (Choice s r notsr bs)
                                            c

  namespace List

    public export
    data Project : (role : typeR)
                -> (bs   : List (typeL, typeM, Global typeR typeL typeM rs g))
                -> (bs'  : List (typeL, typeM, Local  typeR typeL typeM rs g))
                        -> Type
      where
        Empty : Project whom Nil Nil
        Ext : Term.Project whom         x               y
           -> List.Project  whom             xs              ys
           -> List.Project  whom ((xl,xm,x)::xs) ((xl,xm,y)::ys)

  namespace List1

    public export
    data Project : (role : typeR)
                -> (bs   : List1 (typeL, typeM, Global typeR typeL typeM rs g))
                -> (bs'  : List1 (typeL, typeM, Local  typeR typeL typeM rs g))
                        -> Type
      where
        Proj : List.Project  whom (b ::bs) (c ::cs)
            -> List1.Project whom (b:::bs) (c:::cs)

mutual
  namespace Term

    export
    project : DecEq typeR typeL typeM
           => (role  : typeR)
           -> (termG : Global typeR typeL typeM rs g)
                    -> Maybe (termL ** Project role termG termL)
    project role End
      = Just (MkDPair End End)
    project role (Var x)
      = Just (MkDPair (Var x) Var)
    project role T
      = Just (MkDPair T T)
    project role (Rec x) with (project role x)
      project role (Rec x) | (Just (MkDPair fst snd))
        = Just (MkDPair (Rec fst) (Rec snd))

      project role (Rec x) | Nothing
        = Nothing

    project role (Choice s r notSR cs) with (relates role s r notSR)
      project role (Choice role r notSR cs) | (Sends Refl) with (project role cs)
        project role (Choice role r notSR cs) | (Sends Refl) | Nothing
          = Nothing
        project role (Choice role r notSR cs) | (Sends Refl) | (Just (MkDPair cs' prf))
          = Just (Choice SELECT r cs' ** ChoiceSelect Refl prf)

      project role (Choice s role notSR cs) | (Recvs Refl) with (project role cs)
        project role (Choice s role notSR cs) | (Recvs Refl) | Nothing
          = Nothing
        project role (Choice s role notSR cs) | (Recvs Refl) | (Just (MkDPair cs' prf))
          = Just (Choice BRANCH s cs' ** ChoiceBranch Refl prf)

      project role (Choice s r notSR ss) | (Skips prfSNot prfRNot) with (project role ss)
        project role (Choice s r notSR ss) | (Skips prfSNot prfRNot) | Nothing
          = Nothing
        project role (Choice s r notSR ss) | (Skips prfSNot prfRNot) | (Just (MkDPair cs' prf)) with (allSame cs')
          project role (Choice s r notSR ss) | (Skips prfSNot prfRNot) | (Just (MkDPair ((l, (m, c)) ::: cs) prf)) | (Yes (Yes x))
            = Just (c ** ChoiceMerge prfSNot prfRNot prf (Yes x))
          project role (Choice s r notSR ss) | (Skips prfSNot prfRNot) | (Just (MkDPair cs' prf)) | (No contra)
            = Nothing


  namespace List

    export
    project : DecEq typeR typeL typeM
           => (role : typeR)
           -> (bs   : List (typeL, typeM, Global typeR typeL typeM rs g))
                   -> Maybe (bs' ** List.Project role bs bs')

    project role []
      = Just (MkDPair [] Empty)

    project role ((xl,xm,x) :: xs) with (project role x)
      project role ((xl,xm,x) :: xs) | (Just (MkDPair x' prf)) with (List.project role xs)
        project role ((xl,xm,x) :: xs) | (Just (MkDPair x' prf)) | (Just (MkDPair xs' prfs))
          = Just (MkDPair ((xl, (xm, x')) :: xs') (Ext prf prfs))
        project role ((xl,xm,x) :: xs) | (Just (MkDPair x' prf)) | Nothing
          = Nothing
      project role ((xl,xm,x) :: xs) | Nothing
        = Nothing


  namespace List1

    export
    project : DecEq typeR typeL typeM
           => (role  : typeR)
           -> (termG : List1 (typeL, typeM, Global typeR typeL typeM rs g))
                    -> Maybe (termL ** Project role termG termL)
    project role (head ::: tail) with (List.project role (head::tail))
      project role (head ::: tail) | (Just (MkDPair (x :: xs) prfs))
        = Just (MkDPair (x ::: xs) (Proj prfs))
      project role (head ::: tail) | Nothing
        = Nothing

-- [ EOF ]
