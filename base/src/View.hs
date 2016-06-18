module View where

import qualified AnalyseSyntax as A
import qualified Data.Map as M
import qualified Data.Set as S

printConstraints :: A.Constraint -> String
printConstraints xs = M.foldrWithKey (\k a b -> ((show k)  ++ "Superset of " ++ (show $ S.toList a) ++ " ") ++ b) "" xs


class View a where
	view :: a -> String


instance View A.SimpleTy where
	view (A.SVar x) = x
	view (A.SFunction t1 pi t2) = (view t1) ++ " " ++ show pi ++ " ->" ++ (view t2)
	view x = show x