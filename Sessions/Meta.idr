||| We define some meta types that help with specification of syntax.
|||
||| We need some types to facilitate a nameless representation (De Bruijn indicies) for recursion variables.
|||
||| We need types for local branch and selection
module Sessions.Meta

import Decidable.Equality

%default total

public export
data Ty = R -- recursion variable
        | G -- protocol


public export
data ChoiceTy = BRANCH | SELECT

notBS : BRANCH = SELECT -> Void
notBS Refl impossible

export
DecEq ChoiceTy where
  decEq BRANCH BRANCH = Yes Refl
  decEq BRANCH SELECT = No notBS
  decEq SELECT BRANCH = No (negEqSym notBS)
  decEq SELECT SELECT = Yes Refl


-- [ EOF ]
