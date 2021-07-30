||| Views to show how a role interacts, or not, with a Term from a Global Type.
module Sessions.Global.Involved

import Decidable.Equality
import Data.List
import Data.List.Elem

import Data.List1

import Sessions.Meta
import Sessions.Global

%default total

public export
data Relates : (p, s, r : role)
                        -> Type
  where
    Sends : (prfS : role = s)
                 -> Relates role s r

    Recvs : (prfR : role = r)
                 -> Relates role s r

    Skips : (prfSNot : Not (role = s))
         -> (prfRNot : Not (role = r))
                    -> Relates role s r

public export
relates : DecEq role
       => (p, s, r : role)
       -> (contra  : Not (s = r))
                  -> Relates p s r
relates p s r contra with (decEq p s)
  relates p p r contra | (Yes Refl) = (Sends Refl)
  relates p s r contra | (No f) with (decEq p r)
    relates p s p contra | (No f) | (Yes Refl) = (Recvs Refl)
    relates p s r contra | (No f) | (No g) = (Skips f g)


public export
data Involved : role
             -> Global role msg rs g
             -> Type
  where
    Choice : Relates role s r
          -> Involved role (Choice s r sr cs)
    End : Involved role End
    Var : Involved role (Var x)
    T   : Involved role T
    Rec : Involved role (Rec g)

export
involved : DecEq role
          => (p    : role)
          -> (term : Global role msg rs g)
                  -> Involved p term
involved p End      = End
involved p (Var x) = Var
involved p T       = T
involved p (Rec x) = Rec

involved p (Choice s r not cs) with (relates p s r not)
  involved p (Choice s r not cs) | prf = Choice prf

-- [ EOF ]
