module Algorithm where
import AnalyseSyntax
import qualified Ast as A
import qualified Data.Map as M
import qualified Data.Set as S
import Data.List
import Data.Maybe
import Collect


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
modifyTy old newVars (List pi t1) = List pi $ modifyTy old newVars t1
modifyTy old newVars t = t


generalise :: (SimpleTyEnv, SimpleTy) -> SimpleTyScheme 
generalise (env, t) = S.foldr (\a b -> SForall a b) (STys t) vars --SForall vars (STys t) 
	where vars = (collectVarsTy t) `S.difference` (S.foldr (\a b -> (collectVarsTyScheme a) `S.union` b) S.empty $ (S.fromList $ M.elems env))


u :: (SimpleTy, SimpleTy) -> Annotations -> Subst 
u (SNat, SNat) ans = Subst M.empty M.empty
u (SBool, SBool) ans = Subst M.empty M.empty
u (List b1 t1, List b2 t2) ans =  u (t1,t2) ans
u (SPair b1 t1 t2, SPair b2 t3 t4) ans = s2 <> s1
  where 
    s0 = updateTyAnnVar b1 b2
    s1@(Subst st1 sa1) = u (s0 t1,s0 t3) ans 
    s2@(Subst st2 sa2) = u (subst st1 (s0 t2), subst st1 (s0 t4)) ans
u (SFunction t1 b1 t2, SFunction t3 b2 t4) ans = s2 <> s1
	where
		s0 = updateTyAnnVar b1 b2
		s1@(Subst st1 sa1) = u (s0 t1,s0 t3) ans
		s2@(Subst st2 sa2) = u (subst st1 (s0 t2), subst st1 (s0 t4)) ans 
u (SVar x, t) ans = chk (x, t)
u (t, SVar x) ans = chk (x, t)
u (_, _) _ = error "Fail in Unification"


--The chk function a little bit different in comparing to the slides. Instead of returning a bool, it returns the correct substitution.
chk :: (String, SimpleTy) -> Subst
chk (n1, t@(SVar n2)) | n1 == n2       = Subst (M.singleton n1 t) M.empty
chk (n1, t)           | S.notMember n1 $ collectVarsTy t = Subst (M.singleton n1 t) M.empty
chk (n1, t) = error $ "Unfication fail at the chk function var:" ++ n1 ++ " t:" ++ show t


--This is the w algorithm. The major portion of the structure is the same as in the presentation. So, most of the comments are only on places, where it differs from the slide.
w :: (SimpleTyEnv, A.Expr) -> S.Set TyVar -> Annotations -> IO (SimpleTy, Subst, Constraint, S.Set TyVar, Annotations) 
w (env, A.Integer x) vars ann = return (SNat, Subst M.empty M.empty, M.empty, vars, ann)
w (env, A.Bool True) vars ann = return (SBool, Subst M.empty M.empty, M.empty, vars, ann)
w (env, A.Bool False) vars ann = return (SBool, Subst M.empty M.empty, M.empty, vars, ann)
w (env, A.Var x) vars ann = do
                            let t = fromJust $ M.lookup x env --lookup the type from the environment
                                (ty, vars') = instantiate t S.empty vars --Instatiate the t
                            return (ty,
                             Subst M.empty M.empty,
                              M.empty,
                               vars', ann)
w (env, A.Fn pi x t1) vars ann = do
                            let (a1,vars') = freshVar "fn" vars --FreshVar introduces a new variable
                            (t2,s0@(Subst st0 sa0), c, vars'', ann') <- w (M.insert x (STys (SVar a1)) env,t1) vars' ann --insert the x as key in the environment, so that the x could be later used to check its type in env
                            let (b,ann'') = freshAnn (S.insert pi ann') --FreshAnn is introducing a new environment
                            return (SFunction (subst st0 (SVar a1)) b t2,
                                     s0, 
                                     (unionConstraint b (S.singleton pi) c), 
                                     vars'', ann'')
w (env, A.Fun pi f x t1) vars ann = do
                            let (a1, vars') = freshVar "fun" vars
                                (a2, vars'') = freshVar "fun" $ vars'
                                (b,ann') = freshAnn (S.insert pi ann)
                            (t2, s1@(Subst st1 sa1), c, vars''', ann'') <- w (M.insert f (STys $ SFunction (SVar a1) b (SVar a2)) (M.insert x (STys (SVar a1)) env), t1) vars'' ann'
                            let sa1' = substAnnVar sa1
                                s2@(Subst st2 sa2) = u (t2, subst st1 (SVar a2)) ann
                                sa2' = substAnnVar sa2
                            return $ (SFunction (subst st2 $ subst st1 (SVar a1)) (sa2' $ sa1' b) (subst st2 t2),
                             s2 <> s1,
                              (unionConstraint (sa2' $ sa1' b) (S.singleton pi) (substConstraint sa2 c)),
                               vars''', ann'')
w (env, A.App t1 t2) vars ann = do
                            (ty1, s1@(Subst st1 sa1), c1, vars', ann') <- w (env, t1) vars ann
                            (ty2, s2@(Subst st2 sa2), c2, vars'', ann'') <- w (mapEnv st1 env, t2) vars' ann'
                            let (a, vars''') = freshVar "app" vars''
                                (b,ann''') = freshAnn ann''
                                s3@(Subst st3 sa3) = u (subst st2 ty1, SFunction ty2 b (SVar a)) ann
                                sa2' = substConstraint sa2
                                sa3' = substConstraint sa3
                            return (subst st3 (SVar a), 
                                s3 <> s2 <> s1, 
                                unionConstraints (sa3' $ sa2' c1) (sa3' c2), 
                                vars''', ann''')
w (env, A.Let x t1 t2) vars ann = do
                            --Inference the types
                            (ty1, s1@(Subst st1 sa1), c1, vars', ann') <- w (env,t1) vars ann
                            (ty2, s2@(Subst st2 sa2), c2, vars'', ann'')  <- w (mapEnv st1 $ M.insert x (generalise (mapEnv st1 env,ty1)) env , t2) vars' ann'
                            return (ty2,
                             s2 <> s1,
                              unionConstraints (substConstraint sa2 c1) c2,
                               vars'', ann'')
w (env, A.ITE t1 t2 t3) vars ann = do
                            --Inference t1, t2 and t3
                            (ty1, s1@(Subst st1 sa1), c1, vars', ann') <- w (env, t1) vars ann
                            (ty2, s2@(Subst st2 sa2), c2, vars'', ann'') <- w (mapEnv st1 env, t2) vars' ann'
                            (ty3, s3@(Subst st3 sa3), c3, vars''', ann''') <- w (mapEnv st2 (mapEnv st1 env), t3) vars'' ann''
                            --In the first unifcation it checks that ty1 is really of type Bool
                            let s4@(Subst st4 sa4) = u (subst st3 (subst st2 ty1), SBool) ann
                                --The next unfication makes sure that ty3 and ty2 consist of the same type
                                s5@(Subst st5 sa5) = u (subst st4 ty3, subst st4 $ subst st3 ty2) ann
                                sa1' = substConstraint sa1
                                sa2' = substConstraint sa2
                                sa3' = substConstraint sa3
                                sa4' = substConstraint sa4
                                sa5' = substConstraint sa5
                            return (subst st5 (subst st4 ty3),
                             s5 <> s4 <> s3 <> s2 <> s1,
                              unionConstraints (sa5' $ sa4' $ sa3' $ sa2' c1) $ unionConstraints (sa5' $ sa4' $ sa3' c2) (sa5' $ sa4' c3),
                               vars''', ann''')
--In the Oper I just return the SNat as type, because the program only consist of operators that return SNat
w (env, A.Oper op t1 t2) vars ann = do
                            --First inference the types
                            (ty1, s1@(Subst st1 sa1), c1, vars', ann') <- w (env, t1) vars ann
                            (ty2, s2@(Subst st2 sa2), c2, vars'', ann'') <- w (mapEnv st1 env, t2) vars' ann'
                            --Check in the unification that both of the function are of types SNat. I do not check for other types, because there are only operators that produce nats.
                            let s3@(Subst st3 sa3) = u (subst st2 ty1, SNat) ann
                                s4@(Subst st4 sa4) = u (subst st3 ty2, SNat) ann
                                sa1' = substConstraint sa1
                                sa2' = substConstraint sa2
                                sa3' = substConstraint sa3
                                sa4' = substConstraint sa4
                            return (SNat, s2 <> s1,
                             unionConstraints (sa4' $ sa3' $ sa2' c1) (sa4' $ sa3' c2),
                              vars'', ann'')

--The A.pair is used for the Pairs. 
w (env, A.Pair pi t1 t2) vars ann = do
                            let (b1, ann1) = freshAnn ann
                            --inference t1 and t2, such that it can later be used to determine the types of the SPair
                            (ty1, s1@(Subst st1 sa1), c1, vars1, ann2) <- w (env, t1) vars ann1
                            (ty2, s2@(Subst st2 sa2), c2, vars2, ann3) <- w (mapEnv st1 env, t2) vars1 ann2
                            let sa1' = substAnnVar sa1
                                sa2' = substAnnVar sa2
                            return (SPair (sa2' $ sa1' b1) ty1 ty2,
                              s2 <> s1,
                              unionConstraints c1 (unionConstraint (sa2' $ sa1' b1) (S.singleton pi) c2),
                              vars2,
                              ann3)

 
--The APCase is used for the case of Pairs and it can be written like this in a file:
--case t1 of Pair(t2,t3) => t4
w (env, A.PCase t1 x y t2) vars ann = do
                            let (a1, vars1) = freshVar "case" vars
                                (a2, vars2) = freshVar "case" vars1
                                env1 = M.insert x (STys (SVar a1)) $ M.insert y (STys (SVar a2)) env --Inserted x and y, such that it can be later used to check if the unifcation is correct.
                            (ty1, s1@(Subst st1 sa1), c1, vars3 , ann1) <- w (env, t1) vars2 ann
                            putStrLn $ "Env1: " ++ show st1
                            (ty2, s2@(Subst st2 sa2), c2, vars4, ann2) <- w (mapEnv st1 env1, t2) vars3 ann1
                            let (b1, ann3) = freshAnn ann2
                                s3@(Subst st3 sa3) = u (subst st2 $ subst st1 ty1, SPair b1 (SVar a1) (SVar a2)) ann
                                sa1' = substConstraint sa1
                                sa2' = substConstraint sa2
                                sa3' = substConstraint sa3
                            return (
                              ty2,
                              s3 <> s2 <> s1,
                              unionConstraints (sa3' $ sa2' c1) (sa3' c2), 
                              vars4,
                              ann3
                              )
w (env, A.Case t1 x y t2 t3) vars ann = do
                            let (a1, vars1) = freshVar "case" vars
                                (a2, vars2) = freshVar "case" vars1
                                --The env1 is for the x and y variable, so that it can be checked at a later point what the types are.
                                env1 = M.insert x (STys (SVar a1)) $ M.insert y (STys (SVar a2)) env
                            --Next, I inferenced the types of expressions
                            (ty1, s1@(Subst st1 sa1), c1, vars3 , ann1) <- w (env, t1) vars2 ann
                            (ty2, s2@(Subst st2 sa2), c2, vars4, ann2) <- w (mapEnv st1 env1, t2) vars3 ann1
                            (ty3, s3@(Subst st3 sa3), c3, vars5, ann3) <- w (mapEnv st2 $ mapEnv st1 env1, t3) vars4 ann2
                            let (b1, ann4) = freshAnn ann3
                                --The first unification is used to make sure ty1 is really a list.
                                s4@(Subst st4 sa4) = u (subst st2 ty1, List (S.singleton b1) (SVar a2)) ann
                                --The second unification is used to make sure ty2 and ty3 consist of the same types.
                                s5@(Subst st5 sa5) = u (subst st4 ty3, subst st4 $ subst st3 ty2) ann
                                sa1' = substConstraint sa1
                                sa2' = substConstraint sa2
                                sa3' = substConstraint sa3
                                sa4' = substConstraint sa4
                                sa5' = substConstraint sa5
                            return (
                              subst st5 $ subst st4 $ subst st3 $ ty2,
                              s5 <> s4 <> s3 <> s2 <> s1,
                              unionConstraints (sa3' $ sa2' c1) (sa3' c2), 
                              vars4,
                              ann4
                              )
w (env, A.Cons  pi t1 t2) vars ann = do
                            let (b1, ann1) = freshAnn ann 
                            --First I inferenced both the types of t1 t2
                            (ty1, s1@(Subst st1 sa1), c1, vars1, ann2) <- w (env, t1) vars ann1
                            (ty2, s2@(Subst st2 sa2), c2, vars2, ann3) <- w (mapEnv st1 env, t2) vars1 ann2
                            let sa1' = substAnnVar sa1
                                sa2' = substAnnVar sa2
                                --Next I unified the types of ty2 and ty1, to make sure ty2 is reallya list.
                                s3@(Subst st3 sa3) = u (ty2, List (S.singleton pi) (subst st2 ty1)) ann
                            return (List (S.singleton $ sa2' $ sa1' b1) (subst st3 $ subst st2 ty1),
                              s3 <> s2 <> s1,
                              unionConstraints c1 (unionConstraint (sa2' $ sa1' b1) (S.singleton pi) c2),
                              vars2,
                              ann3)
w (env, A.Nil pi) vars ann	= do 
                        let (a1, vars1) = freshVar "nil" vars --makes a new variables, such that it can be used in the List.
                            (b1, ann1) = freshAnn ann
                        return (List (S.singleton pi) (SVar a1), Subst M.empty M.empty, M.singleton b1 (S.singleton pi), vars1, ann1)

--Unions the constraints
unionConstraints :: Constraint -> Constraint -> Constraint
unionConstraints c1 c2 = M.foldWithKey unionConstraint c1 c2

--union an constraint with a different annotation, such that it will not overwrite the old.
unionConstraint :: AnnVar -> Annotations -> Constraint -> Constraint
unionConstraint v ans c = f $ M.lookup v c
	where
		f Nothing  = M.insert v ans c
		f (Just x) = M.insert v (x `S.union` ans) c 

--The updateTyAnvar is just to update a annotation of the SimpleTy To the an new annotation. 
updateTyAnnVar :: AnnVar -> AnnVar -> SimpleTy -> SimpleTy
updateTyAnnVar old new (SFunction t1 var t2) | old == var = SFunction (updateTyAnnVar old new t1) new (updateTyAnnVar old new t1)
										                         | otherwise = SFunction (updateTyAnnVar old new t1) var (updateTyAnnVar old new t1)
updateTyAnnVar old new (SPair pi e1 e2) | pi == old = SPair new e1 e2
                                        | otherwise = SPair pi e1 e2
updateTyAnnVar _ _ t = t

substConstraint :: AnSubst -> Constraint -> Constraint
substConstraint a c = M.mapKeys (\k -> M.findWithDefault k k a) c

substAnnVar :: AnSubst -> AnnVar -> AnnVar
substAnnVar xs a = M.findWithDefault a a xs

subst :: TySubst -> SimpleTy -> SimpleTy
subst s t@(SVar x) = M.findWithDefault t x s
subst s SNat = SNat 
subst s (SFunction t1 x t2) = SFunction (subst s t1) x (subst s t2)
subst s SBool = SBool
subst s (SPair pi t1 t2) = SPair pi (subst s t1) (subst s t2)
subst s (List pi t1) = List pi (subst s t1)


--(<>) is used as composition function for the subs
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