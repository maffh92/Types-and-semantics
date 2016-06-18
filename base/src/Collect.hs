module Collect where

import qualified Ast as A
import qualified Data.Set as S
import AnalyseSyntax


--The collectVarsExpr are used in the main function to collect all the variables from the Expression.
collectVarsExpr :: A.Expr -> S.Set TyVar
collectVarsExpr (A.Var x) = S.singleton x
collectVarsExpr (A.Fn pi x e0) = S.insert x (collectVarsExpr e0)
collectVarsExpr (A.Fun pi f x e0) = S.insert x (collectVarsExpr e0)
collectVarsExpr (A.App e1 e2) = collectVarsExpr e1 `S.union` collectVarsExpr e2
collectVarsExpr (A.Let x e1 e2) = (S.insert x $ collectVarsExpr e1) `S.union` collectVarsExpr e2
collectVarsExpr (A.ITE e1 e2 e3) = collectVarsExpr e1 `S.union` collectVarsExpr e2 `S.union` collectVarsExpr e3
collectVarsExpr (A.Oper op e1 e2) = collectVarsExpr e1 `S.union` collectVarsExpr e2
collectVarsExpr (A.PCase e1 x y e2) = collectVarsExpr e1 `S.union` S.singleton x `S.union` S.singleton y `S.union` collectVarsExpr e2
collectVarsExpr (A.Pair pi e1 e2) = collectVarsExpr e1 `S.union` collectVarsExpr e2
collectVarsExpr (A.Cons pi e1 e2) = collectVarsExpr e1 `S.union` collectVarsExpr e2
collectVarsExpr (A.Case e1 x y e2 e3) =  (collectVarsExpr e1) `S.union` collectVarsExpr e2 `S.union` collectVarsExpr e3
collectVarsExpr e = S.empty

--The collectVarsTy collects all the variables fromt the simpleTy
collectVarsTy :: SimpleTy -> S.Set String
collectVarsTy (SVar x) = S.singleton x
collectVarsTy SBool = S.empty
collectVarsTy SNat = S.empty
collectVarsTy (SFunction t1 a t2) = (collectVarsTy t1) `S.union` (collectVarsTy t2)
collectVarsTy (SPair pi t1 t2) = (collectVarsTy t1) `S.union` (collectVarsTy t2)
collectVarsTy (List pi e1) = collectVarsTy e1

--collecAnnotationCons collects all the annotation variables from the Annotataions
collectAnnotationsCons :: A.Expr -> Annotations
collectAnnotationsCons (A.Fn pi x e0) 	     = collectAnnotationsCons e0
collectAnnotationsCons (A.Fun pi f x e0) 	 = collectAnnotationsCons e0
collectAnnotationsCons (A.App e1 e2) 	     = collectAnnotationsCons e1 `S.union` collectAnnotationsCons e2
collectAnnotationsCons (A.Let x e1 e2) 	     = (collectAnnotationsCons e1) `S.union` collectAnnotationsCons e2
collectAnnotationsCons (A.ITE e1 e2 e3)      = collectAnnotationsCons e1 `S.union` collectAnnotationsCons e2 `S.union` collectAnnotationsCons e3
collectAnnotationsCons (A.Oper op e1 e2)     = collectAnnotationsCons e1 `S.union` collectAnnotationsCons e2
collectAnnotationsCons (A.PCase e1 x y e2)   = collectAnnotationsCons e1 `S.union` collectAnnotationsCons e2
collectAnnotationsCons (A.Pair pi e1 e2) 	 = collectAnnotationsCons e1 `S.union` collectAnnotationsCons e2
collectAnnotationsCons (A.Case e1 x y e2 e3) = (collectAnnotationsCons e1) `S.union` (collectAnnotationsCons e2) `S.union` (collectAnnotationsCons e3)
collectAnnotationsCons (A.Cons  pi e1 e2)	 = S.singleton pi `S.union` (collectAnnotationsCons e1) `S.union` (collectAnnotationsCons e2)
collectAnnotationsCons (A.Nil pi)			 = S.singleton pi
collectAnnotationsCons e 				     = S.empty

--collectVarsTyScheme collects the variables from the Schemes
collectVarsTyScheme :: SimpleTyScheme -> S.Set String
collectVarsTyScheme (SForall x t) = S.insert x $ collectVarsTyScheme t
collectVarsTyScheme (STys t) = collectVarsTy t

--The adjustAnnotation is used to modify all the annotation of the expression to an unique annotation.
adjustAnnotation :: (A.Expr,Annotations) -> (A.Expr,Annotations)
adjustAnnotation (A.Fn pi x e0, ann)   = let
                                        (a,ann1) = freshAnn ann
                                        (e0',ann2) = adjustAnnotation (e0,ann1)
                                        in (A.Fn a x e0', ann2)
adjustAnnotation (A.Fun pi f x e0, ann) = let
                                        (a,ann1) = freshAnn ann
                                        (e0',ann2) = adjustAnnotation (e0,ann1)
                                        in (A.Fun a f x e0', ann2)
adjustAnnotation (A.App e1 e2, ann)     = let
                                        (e1',ann1) = adjustAnnotation (e1,ann)
                                        (e2',ann2) = adjustAnnotation (e2,ann1)
                                        in (A.App e1' e2', ann2)
adjustAnnotation (A.Pair pi e1 e2, ann) = let
                                        (a,ann1) = freshAnn ann
                                        (e1',ann2) = adjustAnnotation (e1,ann1)
                                        (e2',ann3) = adjustAnnotation (e2,ann2)
                                        in (A.Pair a e1' e2', ann3)
adjustAnnotation (A.Let x e1 e2, ann)   = let
                                        (e1',ann1) = adjustAnnotation (e1,ann)
                                        (e2',ann2) = adjustAnnotation (e2,ann1)
                                        in (A.Let x e1' e2', ann2)
adjustAnnotation (A.ITE e1 e2 e3, ann)  = let
                                        (e1',ann1) = adjustAnnotation (e1,ann)
                                        (e2',ann2) = adjustAnnotation (e2,ann1)
                                        (e3',ann3) = adjustAnnotation (e3,ann2)
                                        in (A.ITE e1' e2' e3', ann3)
adjustAnnotation (A.Oper op e1 e2, ann) = let
                                        (e1',ann1) = adjustAnnotation (e1,ann)
                                        (e2',ann2) = adjustAnnotation (e2,ann1)
                                        in (A.Oper op e1' e2', ann2)
adjustAnnotation (A.PCase e1 x y e2, ann)    = let
                                        (e1',ann1) = adjustAnnotation (e1,ann)
                                        (e2',ann2) = adjustAnnotation (e2,ann1)
                                        in (A.PCase e1' x y e2', ann2)
adjustAnnotation (A.Case e1 x y e2 e3, ann)    = let
                                        (e1',ann1) = adjustAnnotation (e1,ann)
                                        (e2',ann2) = adjustAnnotation (e2,ann1)
                                        (e3',ann3) = adjustAnnotation (e3,ann2)
                                        in (A.Case e1' x y e2' e3', ann3)
adjustAnnotation (A.Cons pi e1 e2, ann) = let
                                        (a,ann1) = freshAnn ann
                                        (e1',ann2) = adjustAnnotation (e1,ann1)
                                        (e2',ann3) = adjustAnnotation (e2,ann2)
                                        in (A.Cons a e1' e2', ann3)
adjustAnnotation (A.Nil pi, ann) = let (a,ann1) = freshAnn ann in  (A.Nil a, ann1)
adjustAnnotation t = t

--introduce Fresh variables
freshVar :: String -> S.Set TyVar -> (TyVar, S.Set TyVar)
freshVar x vars = if S.notMember x vars 
                    then (x,S.insert x vars) 
                    else freshVar (x ++ "'") vars

--Introduce fresh variables
freshAnn :: Annotations -> (Integer, Annotations)
freshAnn xs | S.null xs = (0, S.singleton 0)
            | otherwise = let x = (S.findMax xs) + 1 
                          in (x, S.insert x xs)