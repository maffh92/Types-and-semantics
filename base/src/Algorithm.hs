module Algorithm where
import AnalyseSyntax
import qualified Ast as A
import qualified Data.Map as M
import qualified Data.Set as S
import Data.List
import Data.Maybe


instantiate :: SimpleTyScheme -> S.Set TyVar -> S.Set TyVar -> (SimpleTy, S.Set TyVar)
instantiate (SForall x t) fVars totalVars = instantiate t (S.insert x fVars) totalVars
instantiate (STys ty) fVars totalVars = (ty', totalVars `S.union` tVars `S.union` fVars)
							 where 
							 	   ty' = S.foldr (\a b -> modifyTy a fAll b) ty fVars
							 	   (fAll,tVars) = freshVars fVars totalVars

freshVars :: S.Set TyVar -> S.Set TyVar -> (M.Map TyVar TyVar, S.Set TyVar)
freshVars vars tVars = (M.fromList $ zip (S.toList vars) (S.toList fresh'), totalVars)
		where (fresh',totalVars) = S.foldr (\a (fresh,t) -> let (x, total) = freshVar a t 
														 in (S.insert x fresh,total)) 
								  (S.empty,tVars) vars

modifyTy :: TyVar -> M.Map TyVar TyVar -> SimpleTy -> SimpleTy
modifyTy old newVars (SVar x) | old == x = SVar $ M.findWithDefault old old newVars --fromJust $ M.lookup x newVars 
modifyTy old newVars (SFunction t1 a t2) = SFunction (modifyTy old newVars t1) a (modifyTy old newVars t2)
modifyTy old newVars (SPair pi t1 t2) =  SPair pi (modifyTy old newVars t1) (modifyTy old newVars t2)
modifyTy old newVars t = t


generalise :: (SimpleTyEnv, SimpleTy) -> SimpleTyScheme 
generalise (env, t) = S.foldr (\a b -> SForall a b) (STys t) vars --SForall vars (STys t) 
	where vars = (collectVarsTy t) `S.difference` (S.foldr (\a b -> (collectVarsTyScheme a) `S.union` b) S.empty $ (S.fromList $ M.elems env))


u :: (SimpleTy, SimpleTy) -> String -> Subst 
u (SNat, SNat) _ = Subst M.empty M.empty
u (SBool, SBool) _ = Subst M.empty M.empty
u (SPair b1 t1 t2, SPair b2 t3 t4) s = s2 <> s1
  where 
    s0 = updateTyAnnVar b1 b2
    s1@(Subst st1 sa1) = u (s0 t1,s0 t3) "It is because This function"
    s2@(Subst st2 sa2) = u (subst st1 (s0 t2), subst st1 (s0 t4)) s
u (SFunction t1 b1 t2, SFunction t3 b2 t4) s = s2 <> s1
	where
		s0 = updateTyAnnVar b1 b2
		s1@(Subst st1 sa1) = u (s0 t1,s0 t3) "It is because This function"
		s2@(Subst st2 sa2) = u (subst st1 (s0 t2), subst st1 (s0 t4)) s
u (SVar x, t) s = chk (x, t) s
u (t, SVar x) s = chk (x, t) s
u (_, _) _ = error "Fail in Unification"


w :: (SimpleTyEnv, A.Expr) -> S.Set TyVar -> Annotations -> IO (SimpleTy, Subst, Constraint, S.Set TyVar, Annotations) 
w (env, A.Integer x) vars ann = return (SNat, Subst M.empty M.empty, M.empty, vars, ann)
w (env, A.Bool True) vars ann = return (SBool, Subst M.empty M.empty, M.empty, vars, ann)
w (env, A.Bool False) vars ann = return (SBool, Subst M.empty M.empty, M.empty, vars, ann)
w (env, A.Var x) vars ann = do
                            --putStrLn $ "Var:"
                            --putStrLn $ "Var: env: " ++ show env
                            let t = check (M.lookup x env) ("w A.var: There is no " ++ x ++ " in " ++ show env)
                            let (ty, vars') = instantiate t S.empty vars
                            --putStrLn $ "OldVars:" ++ show vars ++ "\nnewVars:" ++ show vars'
                            --putStrLn $ "OldTy: " ++ show t ++ "\n newTy:" ++ show ty
                            return (ty,
                             Subst M.empty M.empty,
                              M.empty,
                               vars', ann)
w (env, A.Fn pi x t1) vars ann = do
                            --putStrLn "Fn:"
                            let (a1,vars') = freshVar "fn" vars
                            (t2,s0@(Subst st0 sa0), c, vars'', ann') <- w (M.insert x (STys (SVar a1)) env,t1) vars' ann
                            let (b,ann'') = freshAnn (S.insert pi ann')
                            return (SFunction (subst st0 (SVar a1)) b t2,
                                     s0, 
                                     (unionConstraint b (S.singleton pi) c), 
                                     vars'', ann'')
w (env, A.Fun pi f x t1) vars ann = do
                                --putStrLn "Fun:"
                            let (a1, vars') = freshVar "fun" vars
                            let (a2, vars'') = freshVar "fun" $ vars'
                            let (b,ann') = freshAnn (S.insert pi ann)
                            (t2, s1@(Subst st1 sa1), c, vars''', ann'') <- w (M.insert f (STys $ SFunction (SVar a1) b (SVar a2)) env, t1) vars'' ann'
                            let sa1' = substAnnVar sa1
                            let s2@(Subst st2 sa2) = u (t2, subst st1 (SVar a2)) ""
                            let sa2' = substAnnVar sa2
                            return $ (SFunction (subst st2 $ subst st1 (SVar a1)) (sa2' $ sa1' b) (subst st2 t2),
                             s2 <> s1,
                              (unionConstraint (sa2' $ sa1' b) (S.singleton pi) (substConstraint sa2 c)),
                               vars''', ann'')
w (env, A.App t1 t2) vars ann = do
                            --putStrLn "App:"
                            (ty1, s1@(Subst st1 sa1), c1, vars', ann') <- w (env, t1) vars ann
                            (ty2, s2@(Subst st2 sa2), c2, vars'', ann'') <- w (mapEnv st1 env, t2) vars' ann'
                            --putStrLn $ show t1 ++ ": " ++ show ty1 ++ "\n" ++ show t2 ++ ": " ++ show ty2
                            let (a, vars''') = freshVar "app" vars''
                            --putStrLn $ "App a:" ++ a ++ " Current vars:" ++ show vars''' 
                            let (b,ann''') = freshAnn ann''
                            let s3@(Subst st3 sa3) = u (subst st2 ty1, SFunction ty2 b (SVar a)) "w app:"
                            let sa2' = substConstraint sa2
                            let sa3' = substConstraint sa3
                            return (subst st3 (SVar a), 
                                s3 <> s2 <> s1, 
                                unionConstraints (sa3' $ sa2' c1) (sa3' c2), 
                                vars''', ann''')
w (env, A.Let x t1 t2) vars ann = do
                            --putStrLn "Let:"
                            (ty1, s1@(Subst st1 sa1), c1, vars', ann') <- w (env,t1) vars ann
                            --putStrLn "Ik ben een let...-----------------------------------------"
                            (ty2, s2@(Subst st2 sa2), c2, vars'', ann'')  <- w (mapEnv st1 $ M.insert x (generalise (mapEnv st1 env,ty1)) env , t2) vars' ann'
                            return (ty2,
                             s2 <> s1,
                              unionConstraints (substConstraint sa2 c1) c2,
                               vars'', ann'')
w (env, A.ITE t1 t2 t3) vars ann = do
                            --putStrLn "ITE:"
                            (ty1, s1@(Subst st1 sa1), c1, vars', ann') <- w (env, t1) vars ann
                            (ty2, s2@(Subst st2 sa2), c2, vars'', ann'') <- w (mapEnv st1 env, t2) vars' ann'
                            (ty3, s3@(Subst st3 sa3), c3, vars''', ann''') <- w (mapEnv st2 (mapEnv st1 env), t3) vars'' ann''
                            let s4@(Subst st4 sa4) = u (subst st3 (subst st2 ty1), SBool) ""
                            let s5@(Subst st5 sa5) = u (subst st4 ty3, subst st4 $ subst st3 ty2) ""
                            let sa1' = substConstraint sa1
                            let sa2' = substConstraint sa2
                            let sa3' = substConstraint sa3
                            let sa4' = substConstraint sa4
                            let sa5' = substConstraint sa5
                            return (subst st5 (subst st4 ty3),
                             s5 <> s4 <> s3 <> s2 <> s1,
                              unionConstraints (sa5' $ sa4' $ sa3' $ sa2' c1) $ unionConstraints (sa5' $ sa4' $ sa3' c2) (sa5' $ sa4' c3),
                               vars''', ann''')
w (env, A.Oper op t1 t2) vars ann = do
                            --putStrLn "Oper"
                            (ty1, s1@(Subst st1 sa1), c1, vars', ann') <- w (env, t1) vars ann
                            (ty2, s2@(Subst st2 sa2), c2, vars'', ann'') <- w (mapEnv st1 env, t2) vars' ann'
                            let s3@(Subst st3 sa3) = u (subst st2 ty1, ty1) ""
                            let s4@(Subst st4 sa4) = u (subst st3 ty2, ty2) ""
                            let sa1' = substConstraint sa1
                            let sa2' = substConstraint sa2
                            let sa3' = substConstraint sa3
                            let sa4' = substConstraint sa4
                            return (SNat, s2 <> s1,
                             unionConstraints (sa4' $ sa3' $ sa2' c1) (sa4' $ sa3' c2),
                              vars'', ann'')
w (env, A.Pair pi t1 t2) vars ann = do
                            let (b1, ann1) = freshAnn ann
                            (ty1, s1@(Subst st1 sa1), c1, vars1, ann2) <- w (env, t1) vars ann1
                            (ty2, s2@(Subst st2 sa2), c2, vars2, ann3) <- w (mapEnv st1 env, t2) vars1 ann2
                            let sa1' = substAnnVar sa1
                            let sa2' = substAnnVar sa2
                            return (SPair (sa2' $ sa1' b1) ty1 ty2,
                              s2 <> s1,
                              unionConstraints c1 (unionConstraint (sa2' $ sa1' b1) (S.singleton pi) c2),
                              vars2,
                              ann3)
 --case t1 of Pair(t2,t3) => t4                          
w (env, A.PCase t1 x y t2) vars ann = do
                            let (a1, vars1) = freshVar "case" vars
                            let (a2, vars2) = freshVar "case" vars1
                            let env1 = M.insert x (STys (SVar a1)) $ M.insert y (STys (SVar a2)) env
                            (ty1, s1@(Subst st1 sa1), c1, vars3 , ann1) <- w (env, t1) vars2 ann
                            putStrLn $ "Env1: " ++ show st1
                            (ty2, s2@(Subst st2 sa2), c2, vars4, ann2) <- w (mapEnv st1 env1, t2) vars3 ann1
                            let (b1, ann3) = freshAnn ann2
                            let s3@(Subst st3 sa3) = u (subst st2 $ subst st1 ty1, SPair b1 (SVar a1) (SVar a2)) "The case of course"
                            let sa1' = substConstraint sa1
                            let sa2' = substConstraint sa2
                            let sa3' = substConstraint sa3
                            return (
                              ty2,
                              s3 <> s2 <> s1,
                              unionConstraints (sa3' $ sa2' c1) (sa3' c2), 
                              vars4,
                              ann3
                              )
w (env, A.Case t1 x y t2 t3) vars ann = do
                            let (a1, vars1) = freshVar "case" vars
                            let (a2, vars2) = freshVar "case" vars1
                            let env1 = M.insert x (STys (SVar a1)) $ M.insert y (STys (SVar a2)) env
                            (ty1, s1@(Subst st1 sa1), c1, vars3 , ann1) <- w (env, t1) vars2 ann
                            putStrLn $ "Env1: " ++ show st1
                            (ty2, s2@(Subst st2 sa2), c2, vars4, ann2) <- w (mapEnv st1 env1, t2) vars3 ann1
                            let (b1, ann3) = freshAnn ann2
                            let s3@(Subst st3 sa3) = u (subst st2 $ subst st1 ty1, Cons b1 (SVar a1) (SVar a2)) "The case of course"
                            let sa1' = substConstraint sa1
                            let sa2' = substConstraint sa2
                            let sa3' = substConstraint sa3
                            return (
                              ty2,
                              s3 <> s2 <> s1,
                              unionConstraints (sa3' $ sa2' c1) (sa3' c2), 
                              vars4,
                              ann3
                              )
w (env, A.Cons  pi t1 t2) vars ann = do
                            let (b1, ann1) = freshAnn ann
                            (ty1, s1@(Subst st1 sa1), c1, vars1, ann2) <- w (env, t1) vars ann1
                            (ty2, s2@(Subst st2 sa2), c2, vars2, ann3) <- w (mapEnv st1 env, t2) vars1 ann2
                            let sa1' = substAnnVar sa1
                            let sa2' = substAnnVar sa2
                            return (Cons [(sa2' $ sa1' b1)] ty1 ty2,
                              s2 <> s1,
                              unionConstraints c1 (unionConstraint (sa2' $ sa1' b1) (S.singleton pi) c2),
                              vars2,
                              ann3)
w (env, A.Nil pi) vars ann	= let (b1, ann1) = freshAnn ann in return (Nil (b1), Subst M.empty M.empty, M.singleton b1 (S.singleton pi), vars, ann1)


In de case bij de list:  is het de bedoeling dat x1 gelijk moet zijn aan e1 en x2 gelijk aan e2. 
case e0 of Cons (x,x2) => e1 or e2

unionConstraints :: Constraint -> Constraint -> Constraint
unionConstraints c1 c2 = M.foldWithKey unionConstraint c1 c2

unionConstraint :: AnnVar -> Annotations -> Constraint -> Constraint
unionConstraint v ans c = f $ M.lookup v c
	where
		f Nothing  = M.insert v ans c
		f (Just x) = M.insert v (x `S.union` ans) c 

insertConstraint :: AnnVar -> Annotations -> Constraint -> Constraint
insertConstraint v ans c = M.insert v ans c

updateTyAnnVar :: AnnVar -> AnnVar -> SimpleTy -> SimpleTy
updateTyAnnVar old new (SFunction t1 var t2) | old == var = SFunction (updateTyAnnVar old new t1) new (updateTyAnnVar old new t1)
										     | otherwise = SFunction (updateTyAnnVar old new t1) var (updateTyAnnVar old new t1)
updateTyAnnVar _ _ t = t

substConstraint :: AnSubst -> Constraint -> Constraint
substConstraint a c = M.mapKeys (\k -> M.findWithDefault k k a) c

substAnnVar :: AnSubst -> AnnVar -> AnnVar
substAnnVar xs a = M.findWithDefault a a xs

subst :: TySubst -> SimpleTy -> SimpleTy
subst s t@(SVar x) = M.findWithDefault t x s --check (M.lookup x s) (" subst: There is no " ++ x ++ " in " ++ show s)
subst s SNat = SNat 
subst s (SFunction t1 x t2) = SFunction (subst s t1) x (subst s t2)
subst s SBool = SBool
subst s (SPair pi t1 t2) = SPair pi (subst s t1) (subst s t2)

check :: (Show a) => Maybe a -> String -> a
check (Just a) _ = a
check _ s = error s

(<>) :: Subst -> Subst -> Subst
(Subst st1 sa1) <> (Subst st2 sa2) = Subst substType substAnnotation
	where 
		  substType = M.map (subst st1) st2 `M.union` st1
		  substAnnotation = M.map (substAnnVar sa1) sa2 `M.union` sa1

mapEnv :: TySubst -> SimpleTyEnv -> SimpleTyEnv
mapEnv st1 env = M.map (updateSimpleScheme st1) env

updateSimpleScheme :: TySubst -> SimpleTyScheme -> SimpleTyScheme
updateSimpleScheme f (SForall x t) = SForall x (updateSimpleScheme f t)
updateSimpleScheme f (STys ty) = STys (subst f ty)

chk :: (String, SimpleTy) -> String -> Subst
chk (n1, t@(SVar n2)) _ | n1 == n2  		 = Subst (M.singleton n1 t) M.empty
chk (n1, t) _           | S.notMember n1 $ collectVarsTy t = Subst (M.singleton n1 t) M.empty
chk (n1, t) s = error $ "Chk: " ++ n1 ++ " t:" ++ show t ++ " This happended because of:" ++ s


--introduce Fresh variables
freshVar :: String -> S.Set TyVar -> (TyVar, S.Set TyVar)
freshVar x vars = if S.notMember x vars 
                    then (x,S.insert x vars) 
                    else freshVar (x ++ "'") vars

freshAnn :: Annotations -> (Integer, Annotations)
freshAnn xs | S.null xs = (0, S.singleton 0)
            | otherwise = let x = (S.findMax xs) + 1 
                          in (x, S.insert x xs)

collectVarsExpr :: A.Expr -> S.Set TyVar
collectVarsExpr (A.Integer x) = S.empty
collectVarsExpr (A.Bool True) = S.empty
collectVarsExpr (A.Bool False) = S.empty
collectVarsExpr (A.Var x) = S.singleton x
collectVarsExpr (A.Fn pi x e0) = S.insert x (collectVarsExpr e0)
collectVarsExpr (A.Fun pi f x e0) = S.insert x (collectVarsExpr e0)
collectVarsExpr (A.App e1 e2) = collectVarsExpr e1 `S.union` collectVarsExpr e2
collectVarsExpr (A.Let x e1 e2) = (S.insert x $ collectVarsExpr e1) `S.union` collectVarsExpr e2
collectVarsExpr (A.ITE e1 e2 e3) = collectVarsExpr e1 `S.union` collectVarsExpr e2 `S.union` collectVarsExpr e3
collectVarsExpr (A.Oper op e1 e2) = collectVarsExpr e1 `S.union` collectVarsExpr e2
collectVarsExpr (A.PCase e1 x y e2) = collectVarsExpr e1 `S.union` S.singleton x `S.union` S.singleton x `S.union` collectVarsExpr e2
collectVarsExpr (A.Pair pi e1 e2) = collectVarsExpr e1 `S.union` collectVarsExpr e2


collectVarsTy :: SimpleTy -> S.Set String
collectVarsTy (SVar x) = S.singleton x
collectVarsTy SBool = S.empty
collectVarsTy SNat = S.empty
collectVarsTy (SFunction t1 a t2) = (collectVarsTy t1) `S.union` (collectVarsTy t2)
collectVarsTy (SPair pi t1 t2) = (collectVarsTy t1) `S.union` (collectVarsTy t2)

collectAnnotationsCons :: A.Expr -> Annotations
collectAnnotationsCons (A.Fn pi x e0) 	     = collectAnnotationsCons e0
collectAnnotationsCons (A.Fun pi f x e0) 	 = collectAnnotationsCons e0
collectAnnotationsCons (A.App e1 e2) 	     = collectAnnotationsCons e1 `S.union` collectAnnotationsCons e2
collectAnnotationsCons (A.Let x e1 e2) 	     = (collectAnnotationsCons e1) `S.union` collectAnnotationsCons e2
collectAnnotationsCons (A.ITE e1 e2 e3)      = collectAnnotationsCons e1 `S.union` collectAnnotationsCons e2 `S.union` collectAnnotationsCons e3
collectAnnotationsCons (A.Oper op e1 e2)     = collectAnnotationsCons e1 `S.union` collectAnnotationsCons e2
collectAnnotationsCons (A.PCase e1 x y e2)   = collectAnnotationsCons e1 `S.union` collectAnnotationsCons e2
collectAnnotationsCons (A.Pair pi e1 e2) 	 = collectAnnotationsCons e1 `S.union` collectAnnotationsCons e2
collectAnnotationsCons (A.PCase e1 x y e2)   = (collectAnnotationsCons e1) `S.union` (collectAnnotationsCons e2)
collectAnnotationsCons (A.Case e1 x y e2 e3) = (collectAnnotationsCons e1) `S.union` (collectAnnotationsCons e2) `S.union` (collectAnnotationsCons e3)
collectAnnotationsCons (A.Cons  pi e1 e2)	 = S.singleton pi `S.union` (collectAnnotationsCons e1) `S.union` (collectAnnotationsCons e2)
collectAnnotationsCons (A.Nil pi)			 = S.singleton pi
collectAnnotationsCons e 				     = S.empty


collectVarsTyScheme :: SimpleTyScheme -> S.Set String
collectVarsTyScheme (SForall x t) = S.insert x $ collectVarsTyScheme t
collectVarsTyScheme (STys t) = collectVarsTy t


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