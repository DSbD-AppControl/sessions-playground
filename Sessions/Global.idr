||| Here we present the syntax for our global types.
||| Global Types present a top-level view of the protocol.
|||
||| We are inspired from the Tech Report 'A Linear Decomposition of Multiparty Sessions for Safe Distributed Programming' (DTRS12-2).
||| The author's note that sending and receiving are special cases of choice.
|||
|||
module Sessions.Global

import Decidable.Equality
import Data.List
import Data.List.Elem

import Data.List1

import Sessions.Meta

%default total


public export
data Global : (role, label, msg : Type)
           -> (rvars : List Ty)
           -> (type  : Ty)
                   -> Type
  where
    End : Global typeR typeL typeM rs G

    Call : Elem R rs -> Global typeR typeL typeM rs R

    Rec : Global typeR typeL typeM (R::rs) R
       -> Global typeR typeL typeM     rs  R

    Choice : (sender, receiver : typeR)
          -> (prf              : Not (sender = receiver))
          -> (choices          : List1 (typeL, typeM, Global typeR typeL typeM rs g))
                              -> Global typeR typeL typeM rs g

public export
Branch : (role, label, msg : Type)
      -> (rvars : List Ty)
      -> (type  : Ty)
               -> Type
Branch role label msg rvars type
  = (label, msg, Global role label msg rvars type)

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
