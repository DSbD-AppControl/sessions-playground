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
import public Sessions.Projection

%default total

public export
data Merge : (this  : List1 (typeL, typeM, Local typeR typeL typeM rs g))
          -> (that  :                      Local typeR typeL typeM rs g)
                   -> Type
  where
    PMerge : (same : All ((cl,cm,c):::cs))
                  -> Merge ((cl,cm,c):::cs) c

public export
merge : DecEq typeR typeL typeM
     => (this : List1 (typeL, typeM, Local typeR typeL typeM rs g))
             -> Maybe (that ** Merge this that)
merge ((l,(m,c)) ::: tail) with (allSame ((l,(m,c)) ::: tail))
  merge ((l,(m,c)) ::: tail) | (Yes prf)
    = Just (c ** PMerge prf)
  merge ((l,(m,c)) ::: tail) | (No contra)
    = Nothing

public export
project : DecEq typeR typeL typeM
       => {rs    : List Ty}
       -> {g     :      Ty}
       -> (role  : typeR)
       -> (termG : Global typeR typeL typeM rs g)
                -> Maybe (termL ** Project Merge role termG termL)
project = Projection.Term.project merge

-- [ EOF ]
