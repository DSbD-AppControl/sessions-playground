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
data Local : (role, msg  : Type)
          -> (rvars : List Ty)
          -> (type  : Ty)
                   -> Type
  where
    End : Local role msg rs G

    Var : Elem R rs -> Local role msg rs R

    T : Local role msg rs R

    Rec : Local role msg (R::rs) R
       -> Local role msg     rs  R

    Choice : (type : ChoiceTy)
          -> (whom : role)
          -> (selections : List1 (msg, Local role msg rs g))
                        -> Local role msg rs g

-- [ EOF ]
