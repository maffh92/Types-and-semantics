module Algorithm where
import AnalyseSyntax
import qualified Ast as A
import qualified Data.Map as M
import Data.List
import Data.Maybe

instantiate :: TyScheme -> Ty
instantiate (Forall x t) = instantiate t 
instantiate (Tys ty) = ty
instantiate _ = error "instantiate does not have this pattern."

generalise :: (TyEnv, Ty) -> TyScheme 
generalise (env, t) = Forall vars (Tys t) 
	where vars = varsTy t \\ (foldr (\a b -> varsTyScheme a ++ b) [] $ M.elems env)

u :: (Ty, Ty) -> TySubst 
u (Nat, Nat) = M.empty
u (Bool, Bool) = M.empty
u (Function t1 t2, Function t3 t4) = s2 <> s1
	where
		s1 = u (t1,t3)
		s2 = u (subst s1 t2, subst s1 t4)
u (Var x, t) = chk (x, t)
u (t, Var x) = chk (x, t)
u (_, _) = error "Fail in Unification"


w :: (TyEnv, A.Expr) -> [TyVar] -> (Ty, TySubst, [TyVar]) 
w (env, A.Integer x) vars = (Nat, M.empty, vars)
w (env, A.Bool True) vars = (Bool, M.empty, vars)
w (env, A.Bool False) vars = (Bool, M.empty, vars)
w (env, A.Var x) vars = (instantiate t, M.empty, vars)
	where t = check (M.lookup x env) ("w A.var: There is no " ++ x ++ "in " ++ show env)
w (env, A.Fn pi x t1) vars = let 
								(a1,vars') = newVar "a" vars
								(t2,s0, vars'') = w (M.insert x (Forall [] $ Tys $ Var a1) env,t1) $ vars'
							in (Function (subst s0 (Var a1)) t2, s0, vars'')
--error $ "a1:" ++ a1 ++ " a2:" ++ a2 --
w (env, A.Fun pi f x t1) vars = let
								(a1, vars') = newVar "a" vars
								(a2, vars'') = newVar "a" $ vars'
								(t2, s1, vars''') = w (M.insert f (Tys $ Function (Var a1) (Var a2)) env, t1) vars''
								s2 = u (t2, subst s1 (Var a2))
							in error "Hello" --(subst s2 (Function (subst s1 (Var a1)) (subst s2 t2)), s2 <> s1, vars''')
w (env, A.App t1 t2) vars = let
								(ty1, s1,vars') = w (env, t1) vars
								(ty2, s2, vars'') = w (mapEnv s1 env, t2) vars'
								(a, vars''') = newVar "a" vars''
								s3 = u (subst s2 ty1, Function ty2 (Var a))
							in (subst s3 (Var a), s3 <> s2 <> s1, vars''')
w (env, A.Let x t1 t2) vars = let
								(ty1, s1, vars') = w (env,t1) vars
								(ty, s2, vars'')  = w (mapEnv s1 $ M.insert x (generalise (mapEnv s1 env,ty1)) env , t2) vars'
								in (ty, s2 <> s1, vars'')
w (env, A.ITE t1 t2 t3) vars = let
								(ty1, s1, vars') = w (env, t1) vars
								(ty2, s2, vars'') = w (mapEnv s1 env, t2) vars'
								(ty3, s3, vars''') = w (mapEnv s2 (mapEnv s1 env), t3) vars''
								s4        = u (subst s3 (subst s2 ty1), Bool)
								s5		  = u (subst s4 (subst s3 ty2), subst s4 ty3)
								in (subst s5 (subst s4 ty3),  s5 <> s4 <> s3 <> s2 <> s1, vars''')
w (env, A.Oper op t1 t2) vars = let
								(ty1, s1, vars') = w (env, t1) vars
								(ty2, s2, vars'') = w (mapEnv s1 env, t2) vars'
								s3		  = u (subst s2 ty1, opToTy op)
								s4 		  = u (subst s3 ty2, opToTy op)
								in (opToTy op, s2 <> s1, vars'')
w _ _ = error "W does not know this pattern"

--helper
opToTy :: A.Op -> Ty
opToTy A.Add = Function (Function Nat Nat) Nat
opToTy A.Sub = Function (Function Nat Nat) Nat
opToTy A.Mul = Function (Function Nat Nat) Nat
opToTy A.Div = Function (Function Nat Nat) Nat

subst :: TySubst -> Ty -> Ty
subst s t@(Var x) = M.findWithDefault t x s --check (M.lookup x s) (" subst: There is no " ++ x ++ " in " ++ show s)
subst s Nat = Nat 
subst s (Function t1 t2) = Function (subst s t1) (subst s t2)
subst s Bool = Bool

check :: (Show a) => Maybe a -> String -> a
check (Just a) _ = a
check _ s = error s

(<>) :: TySubst -> TySubst -> TySubst
s1 <> s2 = M.map (subst s1) s2 `M.union` s1

varsTy :: Ty -> [String]
varsTy (Var x) = [x]
varsTy Bool = []
varsTy Nat = []
varsTy (Function t1 t2) = (varsTy t1) ++ (varsTy t2) 

varsTyScheme :: TyScheme -> [String]
varsTyScheme (Forall x t) = x ++ varsTyScheme t
varsTyScheme (Tys t) = varsTy t

newVar :: String -> [TyVar] -> (TyVar, [TyVar])
newVar x vars = if not $ any (==x) vars 
					then (x,vars ++ [x]) 
					else newVar (x ++ "'") vars

replace :: String -> Ty -> TyEnv -> TyEnv
replace x t env = M.insert x (Tys t) env 

mapEnv :: TySubst -> TyEnv -> TyEnv
mapEnv s1 env = M.map (updateScheme s1) env

updateScheme :: TySubst -> TyScheme -> TyScheme
updateScheme f (Forall x t) = Forall x (updateScheme f t)
updateScheme f (Tys ty) = Tys (subst f ty)

chk :: (String, Ty) -> TySubst
chk (n1, t@(Var n2)) | n1 == n2  		 = substTy n1 t
chk (n1, t) | (not $ elem n1 $ varsTy t) = substTy n1 t
chk (n1, t) = error $ "Chk: " ++ n1 ++ " t:" ++ show t


substTy :: String -> Ty -> TySubst
substTy s Bool 	  = M.empty
substTy s Nat 	  = M.empty
substTy s (Var x) = M.empty
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

{-





u :: (Ty, Ty) -> TySubst 
u (Nat, Nat) = id
u (Bool, Bool) = id
u (Function t1 t2, Function t3 t4) = s2 . s1
	where
		s1 = u (t1,t3)
		s2 = u (s1 t2, s1 t4)
u (Var x, t) = chk (x, t)
u (t, Var x) = chk (x, t)
u (_, _) = error "Fail in Unification"


chk :: (String, Ty) -> TySubst
chk t'@(x, t) 
	| t == (Var x) || (not $ elem x $ varsTy t) = substTy x t
	| otherwise = error "Unification chk not possible"

w :: (TyEnv, A.Expr) -> [TyVar] -> (Ty, TySubst, [TyVar]) 
w (env, A.Integer x) vars = (Nat, id, vars)
w (env, A.Bool True) vars = (Bool, id, vars)
w (env, A.Bool False) vars = (Bool, id, vars)
w (env, A.Var x) vars = (instantiate t, id, vars)
	where t = fromJust $ M.lookup x env
w (env, A.Fn pi x t1) vars = let 
								(a1,vars') = newVar "a" vars
								(t2,s0, vars'') = w (replace x (Var a1) env,t1) $ vars'
							in (Function (s0 (Var a1)) t2, s0, vars'')
w (env, A.Fun pi f x t1) vars = let
								(a1, vars') = newVar "a" vars
								(a2, vars'') = newVar "a" $ vars'
								(t2, s1, vars''') = w (replace f (Function (Var a1) (Var a2)) env, t1) vars''
								s2 = u (t2, s1 (Var a2))
							in (s2 (Function (s1 (Var a1)) (s2 t2)), s2 . s1, vars''')
w (env, A.App t1 t2) vars = let
								(ty1, s1,vars') = w (env, t1) vars
								(ty2, s2, vars'') = w (mapEnv s1 env, t2) vars'
								(a, vars''') = newVar "a" vars''
								s3 = u (s2 ty1, Function ty2 (Var a))
							in (s3 (Var a), s3 . s2 . s1, vars''')
w (env, A.Let x t1 t2) vars = let
								(ty1, s1, vars') = w (env,t1) vars
								(ty, s2, vars'')  = w (mapEnv s1 $ M.insert x (generalise (mapEnv s1 env,ty1)) env , t2) vars'
								in (ty, s2 . s1, vars'')
w (env, A.ITE t1 t2 t3) vars = let
								(ty1, s1, vars') = w (env, t1) vars
								(ty2, s2, vars'') = w (mapEnv s1 env, t2) vars'
								(ty3, s3, vars''') = w (mapEnv s2 (mapEnv s1 env), t3) vars''
								s4        = u (s3 (s2 ty1), Bool)
								s5		  = u (s4 (s3 ty2), s4 ty3)
								in (s5 (s4 ty3),  s5 . s4 . s3 . s2 . s1, vars''')
w (env, A.Oper op t1 t2) vars = let
								(ty1, s1, vars') = w (env, t1) vars
								(ty2, s2, vars'') = w (mapEnv s1 env, t2) vars'
								s3		  = u (s2 ty1, Nat)
								in (ty1, s2 . s1, vars'')

--
--helper functions
replace :: String -> Ty -> TyEnv -> TyEnv
replace x t env = M.insert x (Tys t) env 


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


varsTyScheme :: TyScheme -> [String]
varsTyScheme (Forall x t) = x ++ varsTyScheme t
varsTyScheme (Tys t) = varsTy t



mapEnv :: TySubst -> TyEnv -> TyEnv
mapEnv s1 env = M.map (updateScheme s1) env

updateScheme :: TySubst -> TyScheme -> TyScheme
updateScheme f (Forall x t) = Forall x (updateScheme f t)
updateScheme f (Tys ty) = Tys (f ty)

substTy :: String -> Ty -> TySubst
substTy s t | (Var t) == t = Var s
				  | otherwise = t
substTy s Bool = Bool
substTy s Nat = Nat
substTy s (Function t1 t2) = Function (substTy s t1) (substTy s t2)

substTyScheme :: String -> TyScheme -> TyScheme
substTyScheme var (Tys t) = Tys (substTy var t)
substTyScheme var (Forall x t) = Forall x (substTyScheme var t)


-}