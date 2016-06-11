module AnalyseSyntax where

import qualified Data.Map as M

data SimpleTy =
		  SVar TyVar
		| SNat
		| SBool
		| SFunction SimpleTy Integer SimpleTy
		deriving Show

data SimpleTyScheme = 
		  STys SimpleTy
		| SForall [TyVar] SimpleTyScheme
	    deriving Show

data Ty = 
		  Var TyVar
		| Nat
		| Bool
		| Function Ty Integer Ty
		deriving Show

data TyScheme = 
		  Tys Ty
		| Forall [TyVar] TyScheme
	    deriving Show

data Subst = Subst TySubst AnSubst

type TyVar = String
type TySubst = M.Map TyVar SimpleTy
type AnSubst = M.Map Integer Integer
type TyEnv =  M.Map String TyScheme
type SimpleTyEnv = M.Map TyVar SimpleTyScheme
type AnnVar = Integer
type Annotations = [Integer]

type Constraint = M.Map AnnVar Annotations