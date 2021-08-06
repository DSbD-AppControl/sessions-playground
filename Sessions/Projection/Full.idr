||| Projection based on Full Merge.
|||
||| The Tech Report 'A Linear Decomposition of Multiparty Sessions for Safe Distributed Programming' (DTRS12-2) defines a 'full merge' operation.
||| This merge operation improves the expressiveness of projection compared to Plain Merge.
|||
module Sessions.Projection.Full

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


-- [ EOF ]
