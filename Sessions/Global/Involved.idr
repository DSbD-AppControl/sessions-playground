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
data Involved : (p, s, r : role)
                        -> Type
  where
    Sends : (prfS : role = s)
                 -> Involved role s r

    Recvs : (prfR : role = r)
                 -> Involved role s r

    Skips : (prfSNot : Not (role = s))
         -> (prfRNot : Not (role = r))
                    -> Involved role s r

public export
involved : DecEq role
        => (p, s, r : role)
        -> (contra  : Not (s = r))
                   -> Involved p s r
involved p s r contra with (decEq p s)
  involved p p r contra | (Yes Refl) = (Sends Refl)
  involved p s r contra | (No f) with (decEq p r)
    involved p s p contra | (No f) | (Yes Refl) = (Recvs Refl)
    involved p s r contra | (No f) | (No g) = (Skips f g)



-- [ EOF ]
