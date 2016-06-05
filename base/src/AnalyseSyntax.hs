{-# LANGUAGE ExistentialQuantification #-}

module AnalyseSyntax where

import qualified Data.Map as M

{- 

data Syntax = 
		  T SimpleTy
		| S SimpleTyScheme
		| TyEnv SimpleTyEnv
		| C Constraint
		deriving Show

data SimpleTyScheme = 
		  Tys SimpleTy
		| Forall ForallVar SimpleTyScheme
	    deriving Show

data SimpleTy = 
		  Var ForallVar
		| Nat
		| Bool
		| Function SimpleTy AnnVar SimpleTy
		deriving Show

data Constraint = 
		   Subset [([String],[String])]
		 | Union Constraint Constraint
		 deriving Show

data Ty = 
		  TyVar ForallVar
		| TyN Integer
		| TyB Bool
		| TyFunction SimpleTy AnnVar SimpleTy
data Ann =
		  Set [Integer]
		| UnionAnn Ann Ann
		 deriving Show

type SimpleTyEnv = M.Map String SimpleTyScheme 
type AnnVar = M.Map Integer String

--}
data Ty = 
		  Var TyVar
		| Nat
		| Bool
		| Function Ty Ty
		deriving Show

data TyScheme = 
		  Tys Ty
		| Forall [TyVar] TyScheme
	    deriving Show

type TyVar = String
type TySubst = M.Map TyVar Ty

type TyEnv =  M.Map String TyScheme

data ForallVar = forall s. Show s => FA s
 
instance Show ForallVar where
  show (FA s) = show s