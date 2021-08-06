||| Here we present the syntax for our local types.
||| Local Types present a role-oriented view of the protocol.
|||
||| We are inspired from the Tech Report 'A Linear Decomposition of Multiparty Sessions for Safe Distributed Programming' (DTRS12-2).
||| The author's note that sending and receiving are special cases of select and branch..
|||
|||
module Sessions.Local

import Decidable.Equality
import Data.List
import Data.List.Elem

import Data.List1

import Sessions.Meta


public export
data Local : (role, label, msg  : Type)
          -> (rvars : List Ty)
          -> (type  : Ty)
                   -> Type
  where
    End : Local typeR typeL typeM rs G

    Var : Elem R rs -> Local typeR typeL typeM rs R

    T : Local typeR typeL typeM rs R

    Rec : Local typeR typeL typeM (R::rs) R
       -> Local typeR typeL typeM     rs  R

    Choice : (type : ChoiceTy)
          -> (whom : typeR)
          -> (selections : List1 (typeL, typeM, Local typeR typeL typeM rs g))
                        -> Local typeR typeL typeM rs g


public export
Branch : (role, label, msg : Type)
      -> (rvars : List Ty)
      -> (type  : Ty)
               -> Type
Branch role label msg rvars type
  = (label, msg, Local role label msg rvars type)

public export
Branches : (role, label, msg : Type)
        -> (rvars : List Ty)
        -> (type  : Ty)
                 -> Type
Branches role label msg rvars type
  = List1 (Branch role label msg rvars type)

public export
Branches' : (role, label, msg : Type)
         -> (rvars : List Ty)
         -> (type  : Ty)
                  -> Type
Branches' role label msg rvars type
  = List (Branch role label msg rvars type)

-- [ EOF ]
