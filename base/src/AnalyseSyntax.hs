module AnalyseSyntax where

import qualified Data.Map as M
import qualified Data.Set as S

data SimpleTy =
		  SVar TyVar
		| SNat
		| SBool
		| SFunction SimpleTy Pi SimpleTy
		| SPair Pi SimpleTy SimpleTy
		| List (S.Set Pi) SimpleTy
		deriving (Show, Ord,Eq)

data SimpleTyScheme = 
		  STys SimpleTy
		| SForall TyVar SimpleTyScheme
	    deriving (Show, Ord,Eq)

data Subst = Subst TySubst AnSubst deriving (Show, Ord,Eq)

type TyVar = String
type TySubst = M.Map TyVar SimpleTy
type AnSubst = M.Map Integer Integer
type SimpleTyEnv = M.Map TyVar SimpleTyScheme
type AnnVar = Integer
type Annotations = S.Set AnnVar
type Pi = Integer
type Constraint = M.Map AnnVar Annotations