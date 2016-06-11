module View where

import qualified AnalyseSyntax as A

class View a where
	view :: a -> String

instance View A.Ty where
	view (A.Var x) = x
	view (A.Function t1 pi t2) = (view t1) ++ "->" ++ (view t2)
	view x = show x

instance View A.SimpleTy where
	view (A.SVar x) = x
	view (A.SFunction t1 pi t2) = (view t1) ++ "->" ++ (view t2)
	view x = show x