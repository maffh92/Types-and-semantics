module Algorithm where
import AnalyseSyntax
import qualified Ast as A
import qualified Data.Map as M
import Data.List
import Data.Maybe


instantiate :: SimpleTyScheme -> [TyVar] -> [TyVar] -> (SimpleTy, [TyVar])
instantiate (SForall x t) fVars totalVars = instantiate t (x ++ fVars) totalVars
instantiate (STys ty) fVars totalVars = (ty', fVars)
							 where 
							 	   ty' = foldr (\a b -> modifyTy a fAll b) ty fVars
							 	   (fAll,tVars) = freshVars fVars
instantiate _ _ _ = error "instantiate does not have this pattern."

freshVars :: [TyVar] -> (M.Map TyVar TyVar, [TyVar])
freshVars vars = (M.fromList $ zip vars fresh, totalVars)
		where (fresh,totalVars) = foldr (\a (fresh,t) -> let (x, total) = freshVar a t 
														 in (x : fresh,total)) 
								  ([],vars) vars


modifyTy :: TyVar -> M.Map TyVar TyVar -> SimpleTy -> SimpleTy
modifyTy old newVars (SVar x) | old == x = SVar $ M.findWithDefault old old newVars
modifyTy old newVars (SFunction t1 a t2) = SFunction (modifyTy old newVars t1) a (modifyTy old newVars t2)
modifyTy old newVars t = t


generalise :: (SimpleTyEnv, SimpleTy) -> SimpleTyScheme 
generalise (env, t) = SForall vars (STys t) 
	where vars = sVarsTy t \\ (foldr (\a b -> sVarsTyScheme a ++ b) [] $ M.elems env)

u :: (SimpleTy, SimpleTy) -> Subst 
u (SNat, SNat) = Subst M.empty M.empty
u (SBool, SBool) = Subst M.empty M.empty
u (SFunction t1 b1 t2, SFunction t3 b2 t4) = s2 <> s1
	where
		s0 = updateTyAnnVar b1 b2
		s1@(Subst st1 sa1) = u (s0 t1,s0 t3)
		s2@(Subst st2 sa2) = u (subst st1 (s0 t2), subst st1 (s0 t4))
u (SVar x, t) = chk (x, t)
u (t, SVar x) = chk (x, t)
u (_, _) = error "Fail in Unification"


w :: (SimpleTyEnv, A.Expr) -> [TyVar] -> Annotations -> IO (SimpleTy, Subst, Constraint, [TyVar], Annotations) 
w (env, A.Integer x) vars ann = return (SNat, Subst M.empty M.empty, M.empty, vars, ann)
w (env, A.Bool True) vars ann = return (SBool, Subst M.empty M.empty, M.empty, vars, ann)
w (env, A.Bool False) vars ann = return (SBool, Subst M.empty M.empty, M.empty, vars, ann)
w (env, A.Var x) vars ann = let (ty, vars') = instantiate t [] vars 
							in return (ty, Subst M.empty M.empty, M.empty, vars', ann)
							where t = check (M.lookup x env) ("w A.var: There is no " ++ x ++ "in " ++ show env)

w (env, A.Fn pi x t1) vars ann = do 
								let (a1,vars') = freshVar "a" vars
								(t2,s0@(Subst st0 sa0), c, vars'', ann') <- w (M.insert x (STys $ SVar a1) env,t1) vars' ann
								let (b,ann'') = freshAnn (pi : ann')
								return (SFunction (subst st0 (SVar a1)) b t2, s0, (insertConstraint b [pi] c), vars'', ann'')

w (env, A.Fun pi f x t1) vars ann = do
                                let (a1, vars') = freshVar "a" vars
                                let (a2, vars'') = freshVar "a" $ vars'
                                let (b,ann') = freshAnn (pi : ann)
                                (t2, s1@(Subst st1 sa1), c, vars''', ann'') <- w (M.insert f (STys $ SFunction (SVar a1) b (SVar a2)) env, t1) vars'' ann'
                                let sa1' = substAnnVar sa1
                                let s2@(Subst st2 sa2) = u (t2, subst st1 (SVar a2))
                                let sa2' = substAnnVar sa2
                                return $ (SFunction (subst st2 $ subst st1 (SVar a1)) (sa2' $ sa1' b) (subst st2 t2), s2 <> s1, (insertConstraint (sa2' $ sa1' b) [pi] c), vars''', ann'')

w (env, A.App t1 t2) vars ann = do
                            let matthew = "hoi"
                            (ty1, s1@(Subst st1 sa1), c1, vars', ann') <- w (env, t1) vars ann
                            (ty2, s2@(Subst st2 sa2), c2, vars'', ann'') <- w (mapEnv st1 env, t2) vars' ann'
                            let (a, vars''') = freshVar "a" vars''
                            let s3@(Subst st3 sa3) = u (subst st2 ty1, SFunction ty2 0 (SVar a))
                            return (subst st3 (SVar a), s3 <> s2 <> s1, M.empty, vars''', ann'')

w (env, A.Let x t1 t2) vars ann = do
								(ty1, s1@(Subst st1 sa1), c1, vars', ann') <- w (env,t1) vars ann
								(ty, s2@(Subst st2 sa2), c2, vars'', ann'')  <- w (mapEnv st1 $ M.insert x (generalise (mapEnv st1 env,ty1)) env , t2) vars' ann'
								return (ty, s2 <> s1, M.empty, vars'', ann'')

w (env, A.ITE t1 t2 t3) vars ann = do
                                (ty1, s1@(Subst st1 sa1), c1, vars', ann') <- w (env, t1) vars ann
                                (ty2, s2@(Subst st2 sa2), c2, vars'', ann'') <- w (mapEnv st1 env, t2) vars' ann'
                                (ty3, s3@(Subst st3 sa3), c3, vars''', ann''') <- w (mapEnv st2 (mapEnv st1 env), t3) vars'' ann''
                                let s4@(Subst st4 sa4) = u (subst st3 (subst st2 ty1), SBool)
                                let s5@(Subst st5 sa5) = u (subst st4 (subst st3 ty2), subst st4 ty3)
                                return (subst st5 (subst st4 ty3),  s5 <> s4 <> s3 <> s2 <> s1, M.empty, vars''', ann''')


w (env, A.Oper op t1 t2) vars ann = do
                                (ty1, s1@(Subst st1 sa1), c1, vars', ann') <- w (env, t1) vars ann
                                (ty2, s2@(Subst st2 sa2), c2, vars'', ann'') <- w (mapEnv st1 env, t2) vars' ann'
                                let s3@(Subst st3 sa3) = u (subst st2 ty1, exprToTy t1)
                                let s4@(Subst st4 sa4) = u (subst st3 ty2, exprToTy t2)
                                return (opToTy op, s2 <> s1, M.empty , vars'', ann'')
w _ _ _ = error "W does not know this pattern"

--helper
opToTy :: A.Op -> SimpleTy
opToTy A.Add = SFunction (SFunction SNat 0 SNat) 0 SNat
opToTy A.Sub = SFunction (SFunction SNat 0 SNat) 0 SNat
opToTy A.Mul = SFunction (SFunction SNat 0 SNat) 0 SNat
opToTy A.Div = SFunction (SFunction SNat 0 SNat) 0 SNat

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
		  substAnnotation = M.empty

varsTy :: Ty -> [String]
varsTy (Var x) = [x]
varsTy Bool = []
varsTy Nat = []
varsTy (Function t1 a t2) = (varsTy t1) ++ (varsTy t2) 

sVarsTy :: SimpleTy -> [String]
sVarsTy (SVar x) = [x]
sVarsTy SBool = []
sVarsTy SNat = []
sVarsTy (SFunction t1 a t2) = (sVarsTy t1) ++ (sVarsTy t2)

varsTyScheme :: TyScheme -> [String]
varsTyScheme (Forall x t) = x ++ varsTyScheme t
varsTyScheme (Tys t) = varsTy t

sVarsTyScheme :: SimpleTyScheme -> [String]
sVarsTyScheme (SForall x t) = x ++ sVarsTyScheme t
sVarsTyScheme (STys t) = sVarsTy t

freshVar :: String -> [TyVar] -> (TyVar, [TyVar])
freshVar x vars = if not $ any (==x) vars 
					then (x,vars ++ [x]) 
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

chk :: (String, SimpleTy) -> Subst
chk (n1, t@(SVar n2)) | n1 == n2  		 = Subst (substTy n1 t) M.empty
chk (n1, t) | (not $ elem n1 $ sVarsTy t) = Subst (substTy n1 t) M.empty
chk (n1, t) = error $ "Chk: " ++ n1 ++ " t:" ++ show t


substTy :: String -> SimpleTy -> TySubst
substTy s SBool 	  = M.empty
substTy s SNat 	  = M.empty
substTy s (SVar x) = M.empty
substTy s t 	  = M.singleton s t

varsExpr :: A.Expr -> [TyVar]
varsExpr (A.Integer x) = []
varsExpr (A.Bool True) = []
varsExpr (A.Bool False) = []
varsExpr (A.Var x) = [x]
varsExpr (A.Fn pi x e0) = x : (varsExpr e0)
varsExpr (A.Fun pi f x e0) = x : (varsExpr e0)
varsExpr (A.App e1 e2) = varsExpr e1 ++ varsExpr e2
varsExpr (A.Let x e1 e2) = x : varsExpr e1 ++ varsExpr e2
varsExpr (A.ITE e1 e2 e3) = varsExpr e1 ++ varsExpr e2 ++ varsExpr e3
varsExpr (A.Oper op e1 e2) = varsExpr e1 ++ varsExpr e2


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