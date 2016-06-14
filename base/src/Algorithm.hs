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
vars :: S.Set TyVar
vars = S.fromList ["a","b","c"]

modifyTy :: TyVar -> M.Map TyVar TyVar -> SimpleTy -> SimpleTy
modifyTy old newVars (SVar x) | old == x = SVar $ M.findWithDefault old old newVars --fromJust $ M.lookup x newVars 
modifyTy old newVars (SFunction t1 a t2) = SFunction (modifyTy old newVars t1) a (modifyTy old newVars t2)
modifyTy old newVars t = t


generalise :: (SimpleTyEnv, SimpleTy) -> SimpleTyScheme 
generalise (env, t) = S.foldr (\a b -> SForall a b) (STys t) vars --SForall vars (STys t) 
	where vars = (sVarsTy t) `S.difference` (S.foldr (\a b -> (sVarsTyScheme a) `S.union` b) S.empty $ (S.fromList $ M.elems env))


func = SForall "a" (STys (SFunction (SVar "a") 3 (SVar "i")))
func' = SFunction (SVar "z") 3 (SVar "e")
funcEnv :: SimpleTyEnv
funcEnv = M.fromList [("a",func)]

u :: (SimpleTy, SimpleTy) -> String -> Subst 
u (SNat, SNat) _ = Subst M.empty M.empty
u (SBool, SBool) _ = Subst M.empty M.empty
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
                            let t = check (M.lookup x env) ("w A.var: There is no " ++ x ++ "in " ++ show env)
                            let (ty, vars') = instantiate t S.empty vars
                            --putStrLn $ "OldVars:" ++ show vars ++ "\nnewVars:" ++ show vars'
                            --putStrLn $ "OldTy: " ++ show t ++ "\n newTy:" ++ show ty
                            return (ty, Subst M.empty M.empty, M.empty, vars', ann)
w (env, A.Fn pi x t1) vars ann = do
                                --putStrLn "Fn:"
                                let (a1,vars') = freshVar "fn" vars
                                (t2,s0@(Subst st0 sa0), c, vars'', ann') <- w (M.insert x (STys (SVar a1)) env,t1) vars' ann
                                let (b,ann'') = freshAnn (pi : ann')
                                return (SFunction (subst st0 (SVar a1)) b t2, s0, (insertConstraint b [pi] c), vars'', ann'')

w (env, A.Fun pi f x t1) vars ann = do
                                --putStrLn "Fun:"
                                let (a1, vars') = freshVar "fun" vars
                                let (a2, vars'') = freshVar "fun" $ vars'
                                let (b,ann') = freshAnn (pi : ann)
                                (t2, s1@(Subst st1 sa1), c, vars''', ann'') <- w (M.insert f (STys $ SFunction (SVar a1) b (SVar a2)) env, t1) vars'' ann'
                                let sa1' = substAnnVar sa1
                                let s2@(Subst st2 sa2) = u (t2, subst st1 (SVar a2)) ""
                                let sa2' = substAnnVar sa2
                                return $ (SFunction (subst st2 $ subst st1 (SVar a1)) (sa2' $ sa1' b) (subst st2 t2), s2 <> s1, (insertConstraint (sa2' $ sa1' b) [pi] c), vars''', ann'')
w (env, A.App t1 t2) vars ann = do
                            --putStrLn "App:"
                            (ty1, s1@(Subst st1 sa1), c1, vars', ann') <- w (env, t1) vars ann
                            (ty2, s2@(Subst st2 sa2), c2, vars'', ann'') <- w (mapEnv st1 env, t2) vars' ann'
                            --putStrLn $ show t1 ++ ": " ++ show ty1 ++ "\n" ++ show t2 ++ ": " ++ show ty2
                            let (a, vars''') = freshVar "app" vars''
                            --putStrLn $ "App a:" ++ a ++ " Current vars:" ++ show vars''' 
                            let (b,ann''') = freshAnn ann''
                            let s3@(Subst st3 sa3) = u (subst st2 ty1, SFunction ty2 b (SVar a)) "w app:"
                            return (subst st3 (SVar a), s3 <> s2 <> s1, M.empty, vars''', ann''')
w (env, A.Let x t1 t2) vars ann = do
                                --putStrLn "Let:"
                                (ty1, s1@(Subst st1 sa1), c1, vars', ann') <- w (env,t1) vars ann
                                --putStrLn "Ik ben een let...-----------------------------------------"
                                (ty2, s2@(Subst st2 sa2), c2, vars'', ann'')  <- w (mapEnv st1 $ M.insert x (generalise (mapEnv st1 env,ty1)) env , t2) vars' ann'
                                return (ty2, s2 <> s1, M.empty, vars'', ann'')

w (env, A.ITE t1 t2 t3) vars ann = do
                                --putStrLn "ITE:"
                                (ty1, s1@(Subst st1 sa1), c1, vars', ann') <- w (env, t1) vars ann
                                (ty2, s2@(Subst st2 sa2), c2, vars'', ann'') <- w (mapEnv st1 env, t2) vars' ann'
                                (ty3, s3@(Subst st3 sa3), c3, vars''', ann''') <- w (mapEnv st2 (mapEnv st1 env), t3) vars'' ann''
                                let s4@(Subst st4 sa4) = u (subst st3 (subst st2 ty1), SBool) ""
                                let s5@(Subst st5 sa5) = u (subst st4 (subst st3 ty2), subst st4 ty3) ""
                                return (subst st5 (subst st4 ty3),  s5 <> s4 <> s3 <> s2 <> s1, M.empty, vars''', ann''')
w (env, A.Oper op t1 t2) vars ann = do
                                --putStrLn "Oper"
                                (ty1, s1@(Subst st1 sa1), c1, vars', ann') <- w (env, t1) vars ann
                                (ty2, s2@(Subst st2 sa2), c2, vars'', ann'') <- w (mapEnv st1 env, t2) vars' ann'
                                let s3@(Subst st3 sa3) = u (subst st2 ty1, ty1) ""
                                let s4@(Subst st4 sa4) = u (subst st3 ty2, ty2) ""
                                return (SNat, s2 <> s1, M.empty , vars'', ann'')


addConstraint :: AnnVar -> Annotations -> Constraint -> Constraint
addConstraint v ans c = f $ M.lookup v c
	where
		f Nothing  = M.insert v ans c
		f (Just x) = M.insert v (x ++ ans) c 

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

check :: (Show a) => Maybe a -> String -> a
check (Just a) _ = a
check _ s = error s

(<>) :: Subst -> Subst -> Subst
(Subst st1 sa1) <> (Subst st2 sa2) = Subst substType substAnnotation
	where 
		  substType = M.map (subst st1) st2 `M.union` st1
		  substAnnotation = M.map (substAnnVar sa1) sa2 `M.union` sa1

varsTy :: Ty -> [String]
varsTy (Var x) = [x]
varsTy Bool = []
varsTy Nat = []
varsTy (Function t1 a t2) = (varsTy t1) ++ (varsTy t2) 

sVarsTy :: SimpleTy -> S.Set String
sVarsTy (SVar x) = S.singleton x
sVarsTy SBool = S.empty
sVarsTy SNat = S.empty
sVarsTy (SFunction t1 a t2) = (sVarsTy t1) `S.union` (sVarsTy t2)

varsTyScheme :: TyScheme -> [String]
varsTyScheme (Forall x t) = x ++ varsTyScheme t
varsTyScheme (Tys t) = varsTy t

sVarsTyScheme :: SimpleTyScheme -> S.Set String
sVarsTyScheme (SForall x t) = S.insert x $ sVarsTyScheme t
sVarsTyScheme (STys t) = sVarsTy t

freshVar :: String -> S.Set TyVar -> (TyVar, S.Set TyVar)
freshVar x vars = if S.notMember x vars 
					then (x,S.insert x vars) 
					else freshVar (x ++ "'") vars

freshAnn :: Annotations -> (Integer, Annotations)
freshAnn xs = (x, x : xs)
	where x = (maximum xs) + 1

replace :: String -> Ty -> TyEnv -> TyEnv
replace x t env = M.insert x (Tys t) env 

mapEnv :: TySubst -> SimpleTyEnv -> SimpleTyEnv
mapEnv st1 env = M.map (updateSimpleScheme st1) env

updateSimpleScheme :: TySubst -> SimpleTyScheme -> SimpleTyScheme
updateSimpleScheme f (SForall x t) = SForall x (updateSimpleScheme f t)
updateSimpleScheme f (STys ty) = STys (subst f ty)

chk :: (String, SimpleTy) -> String -> Subst
chk (n1, t@(SVar n2)) _ | n1 == n2  		 = Subst (substTy n1 t) M.empty
chk (n1, t) _           | S.notMember n1 $ sVarsTy t = Subst (substTy n1 t) M.empty
chk (n1, t) s = error $ "Chk: " ++ n1 ++ " t:" ++ show t ++ " This happended because of:" ++ s

fun :: SimpleTy
fun = SFunction (SVar "d") 3 (SVar "e")

substTy :: String -> SimpleTy -> TySubst
substTy s SBool    = M.empty
substTy s SNat 	   = M.empty
substTy s (SVar x) = M.empty
substTy s t 	   = M.singleton s t

varsExpr :: A.Expr -> S.Set TyVar
varsExpr (A.Integer x) = S.empty
varsExpr (A.Bool True) = S.empty
varsExpr (A.Bool False) = S.empty
varsExpr (A.Var x) = S.singleton x
varsExpr (A.Fn pi x e0) = S.insert x (varsExpr e0)
varsExpr (A.Fun pi f x e0) = S.insert x (varsExpr e0)
varsExpr (A.App e1 e2) = varsExpr e1 `S.union` varsExpr e2
varsExpr (A.Let x e1 e2) = (S.insert x $ varsExpr e1) `S.union` varsExpr e2
varsExpr (A.ITE e1 e2 e3) = varsExpr e1 `S.union` varsExpr e2 `S.union` varsExpr e3
varsExpr (A.Oper op e1 e2) = varsExpr e1 `S.union` varsExpr e2

annotationExpr :: A.Expr -> Annotations
annotationExpr (A.Fn pi x e0) = pi : (annotationExpr e0)
annotationExpr (A.Fun pi f x e0) = pi : (annotationExpr e0)
annotationExpr e = []

exprToTy :: A.Expr -> SimpleTy
exprToTy (A.Integer x) = SNat
exprToTy (A.Bool True) = error "No support for bools"
exprToTy (A.Bool False) = error "No Support for bools"
exprToTy (A.Var x) = SNat
exprToTy (A.Fn pi x e0) = SFunction SNat pi (exprToTy e0)
exprToTy (A.Fun pi f x e0) = SFunction SNat pi (exprToTy e0)
exprToTy (A.App e1 e2) = SBool
exprToTy (A.Let x e1 e2) = SNat
exprToTy (A.ITE e1 e2 e3) = SNat
exprToTy (A.Oper op e1 e2) = SNat