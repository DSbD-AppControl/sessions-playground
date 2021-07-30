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
data Global : (role, msg : Type)
           -> (rvars : List Ty)
           -> (type  : Ty)
                   -> Type
  where
    End : Global role msg rs G

    Var : Elem R rs -> Global role msg rs R

    T : Global role msg rs R

    Rec : Global role msg (R::rs) R
       -> Global role msg     rs  R

    Choice : (sender, receiver : role)
          -> (prf : Not (sender = receiver))
          -> (choices : List1 (msg, Global role msg rs g))
                     -> Global role msg rs g


-- [ EOF ]
