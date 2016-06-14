
func = SForall "a" (STys (SFunction (SVar "a") 3 (SVar "i")))
func' = SFunction (SVar "z") 3 (SVar "e")
funcEnv :: SimpleTyEnv
funcEnv = M.fromList [("a",func)]
fun :: SimpleTy
fun = SFunction (SVar "d") 3 (SVar "e")

vars :: S.Set TyVar
vars = S.fromList ["a","b","c"]

varsTy :: Ty -> [String]
varsTy (Var x) = [x]
varsTy Bool = []
varsTy Nat = []
varsTy (Function t1 a t2) = (varsTy t1) ++ (varsTy t2) 


varsTyScheme :: TyScheme -> [String]
varsTyScheme (Forall x t) = x ++ varsTyScheme t
varsTyScheme (Tys t) = varsTy t


replace :: String -> Ty -> TyEnv -> TyEnv
replace x t env = M.insert x (Tys t) env 