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

import public Sessions.Projection.Error

%default total

mutual
  public export
  projects : DecEq role
          => DecEq msg
          => (whom : role)
          -> (type : List (Pair msg (Global role msg rs g)))
                  -> Either Error (List (Pair msg (Local role msg rs g)))
  projects whom []
    = pure Nil
  projects whom ((type, x) :: xs)
    = do x' <- project whom x
         xs' <- projects whom xs
         pure ((type, x') :: xs')

  public export
  projects1 : DecEq role
           => DecEq msg
           => (whom : role)
           -> (type : List1 (Pair msg (Global role msg rs g)))
                   -> Either Error (List1 (Pair msg (Local role msg rs g)))
  projects1 whom ((type, x) ::: tail)
    = do x' <- project whom x
         xs' <- projects whom tail
         pure ((type, x') ::: xs')

  public export
  project : DecEq role
         => DecEq msg
         => (whom : role)
         -> (type : Global role msg rs g)
                 -> Either Error (Local  role msg rs g)
  project whom End = Right End
  project whom (Var x) = Right (Var x)
  project whom T = Right T
  project whom (Rec x) with (project whom x)
    project whom (Rec x) | (Right prf) = Right (Rec prf)
    project whom (Rec x) | (Left err) = Left err
  project whom (Choice s r notsr cs) with (relates whom s r notsr)
    project whom (Choice s r notsr cs) | (Sends prfS) with (projects1 whom cs)

      project whom (Choice s r notsr cs) | (Sends prfS) | (Left err) = Left err
      project whom (Choice s r notsr cs) | (Sends prfS) | (Right x)
        = Right (Choice SELECT r x)

    project whom (Choice s r notsr cs) | (Recvs prfR) with (projects1 whom cs)
      project whom (Choice s r notsr cs) | (Recvs prfR) | (Left err) = Left err
      project whom (Choice s r notsr cs) | (Recvs prfR) | (Right x)
        = Right (Choice BRANCH s x)

    project whom (Choice s r notsr cs) | (Skips prfSNot prfRNot) with (projects1 whom cs)
      project whom (Choice s r notsr cs) | (Skips prfSNot prfRNot) | (Left err) = Left err
      project whom (Choice s r notsr cs) | (Skips prfSNot prfRNot) | (Right x) with (List1.allSame x)
        project whom (Choice s r notsr cs) | (Skips prfSNot prfRNot) | (Right ((t, c) ::: _)) | (Yes (All y))
          = Right c
        project whom (Choice s r notsr cs) | (Skips prfSNot prfRNot) | (Right x) | (No contra)
          = Left InvalidBranch

-- [ EOF ]
