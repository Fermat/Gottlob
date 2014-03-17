{-# LANGUAGE NamedFieldPuns  #-}
module Language.FTypeInference where
import Language.Syntax
import Language.DependencyAnalysis
import Language.PrettyPrint
import Language.Monad
import Text.PrettyPrint
import Control.Monad.Reader
import Control.Monad.Error
import Control.Monad.State
import Control.Monad.Identity
import qualified Data.Map as M
import Data.List

data TScheme = Scheme [VName] FType deriving (Show)

-- type TCMonad a =ReaderT [Decl] (StateT TypeEnv (ErrorT PCError IO)) a
-- data TypeEnv = TypeEnv{typeDef:: M.Map VName TScheme}
--              deriving Show

-- emptyTEnv :: TypeEnv
-- emptyTEnv = TypeEnv {typeDef = M.empty}

-- extendTypeDef :: VName -> TScheme -> TypeEnv -> TypeEnv
-- extendTypeDef v t e@(TypeEnv {typeDef}) = e{typeDef = M.insert v t typeDef}


toTScheme :: [Decl] -> FType -> TScheme
toTScheme env ft = 
  Scheme [ x | x <- freeVar ft, not (def x env)] ft

-- type TConstraints = [(FType, FType)]
type Subst = [(VName, FType)]
type TypeCxt a = StateT Int (StateT Subst (ReaderT [(VName, TScheme)] (ReaderT [Decl] (ErrorT PCError IO)))) a

tcError :: Disp d => d -> [(Doc, Doc)] -> TypeCxt a
tcError summary details = throwError (ErrMsg [ErrInfo (disp summary) details])

withInfo :: (Disp d) => d -> [(Doc, Doc)] -> TypeCxt a -> TypeCxt a
withInfo summary details m = m `catchError` (throwError . addErrorInfo summary details)

--ReaderT [Decl]
-- data UniError a = UError a a
--                 | Others Doc
--                deriving (Show)

-- instance Disp a => Error (UniError a) where
--   strMsg x = Others $ text x
--   noMsg = strMsg "<unknown>"

-- unification
combine :: Subst -> Subst -> Subst
combine s1 s2 = s1 ++ [(v, apply s1 t) | (v, t) <- s2]

-- no other Side effect other than error
unify :: FType -> FType -> TypeCxt Subst
unify (Arrow t1 t2) (Arrow a1 a2) = do
  s1 <- unify t1 a1
  s2 <- unify (apply s1 t2) (apply s1 a2)
  return $ combine s2 s1
unify (FCons x args1) (FCons y args2)
  | x == y = 
    unifyl (zip args1 args2)
  | otherwise = tcError "Unification failure:"
           [(disp "unify", disp x),(disp "with", disp y)]
  where unifyl eqs = foldM helper [] eqs
        helper sub (ArgType p1, ArgType p2) = 
          unify (apply sub p1) (apply sub p2)
        helper sub (a, b) = 
          tcError "Can't unify the following formal types"
           [(disp "unify", disp a),(disp "with", disp b)]

unify (FVar tn) t = varBind tn t
unify t (FVar tn) = varBind tn t
unify t t' = tcError "Can't unify the following formal types"
           [(disp "unify", disp t),(disp "with", disp t')]

varBind x t | t == FVar x = return []
            | x `elem` freeVar t =
                tcError "Can't unify the infinite formal types"
                [(disp "unify", disp x),(disp "with", disp t)]
            | otherwise = return [(x, t)]

-- side effect: modifying current substitution.
unification :: FType -> FType -> TypeCxt ()
unification t1 t2 = do
  subs <- lift get
  new <- unify (apply subs t1) (apply subs t2)
  lift $ put $ combine new subs
  
arrow a b = Arrow a b

apply :: Subst -> FType -> FType 
apply subs (FVar x) =
  case lookup x subs of
    Just x1 -> x1
    Nothing -> FVar x
apply subs (Arrow f1 f2) =
  let a1 = apply subs f1
      a2 = apply subs f2 in
  Arrow a1 a2

apply subs (FCons c args) =
  FCons c (map (helper subs) args)
  where helper subs (ArgType f) = ArgType (apply subs f)
        helper subs (ArgProg p) = ArgProg p
        
apply subs (FTPos p f2) =
  FTPos p (apply subs f2)

-- modifying int
freshInst :: TScheme -> TypeCxt FType
freshInst (Scheme xs t) =
  if null xs
  then return t
  else do
   newVars <- mapM (\ x -> makeName "`T") xs
   let substs = zip xs (map (\ y -> FVar y) newVars) in
    return $ apply substs t

-- modifying int
makeName :: VName -> TypeCxt VName
makeName name = do
  m <- get
  modify (+1)
  return $ name ++ show m

-- pattern included, modifying TypeCxt accordingly 
checkExpr :: Prog -> TypeCxt (FType, [(VName, TScheme)])
checkExpr (Name x) = do
  tdefs <- ask 
  case lookup x tdefs of
    Just sc -> do
      ft <- freshInst sc
      return (ft, [])
    Nothing -> do
      name <- makeName "`T"
--      lift $ put $ (x, Scheme [] (FVar name)):tdefs
      return (FVar name, [(x, Scheme [] (FVar name))])

checkExpr ap@(Applica t1 t2) = do
  (ty1, as1) <- checkExpr t1
  (ty2, as2) <- local (\y -> as1 ++ y) $ checkExpr t2
  m <- makeName "`T"
  withInfo "During unification" [(disp "in the expression ", disp ap )] (unification ty1 $ Arrow ty2 (FVar m)) 
  return (FVar m, as1 ++ as2)
  
checkExpr (Abs xs t) = do
  ls <- mapM (\ x -> makeName "`T") xs
  let scs = map (\ y -> Scheme [] (FVar y)) ls
      tys = map (\ y -> FVar y) ls
      new = zip xs scs
  (ty, as) <- local (\y -> new++y) $ checkExpr t
--  lift $ modify (\ y -> new ++ y)
  return (foldr arrow ty tys, as)

checkExpr (Match p branches) = do
  (tp, as) <- checkExpr p
  let l = map toEq branches
--  mapM_ (helper tp) l
      (l1, l2) = head l
  (c, as1) <- checkExpr l1
  (init, as2) <- local (\y -> as1 ++ as ++ y) $ checkExpr l2
  unification c tp
  newAs <- foldM (helper c init as) (as2++as) (tail l)
  return (init, newAs)
  where toEq (v, xs, p) =
          let a = foldl' (\ a b -> Applica a b) (Name v) xs
              in (a, p)
        helper c init as curr (a, b) = do
          (t1, a1 ) <- checkExpr a
          unification c t1
          (t2, a2) <- local (\y -> a1 ++ curr ++ y) $ checkExpr b
          unification init t2
          return (a2++curr)

checkExpr (Let xs p) = do
  newAs <- foldM helper [] xs
--  lift $ modify (\ y -> assump ++ y)
  sub <- lift get
  env <- lift $ lift $ lift ask
  local (\ y -> (smartSub env sub newAs) ++ y) $ checkExpr p
  where helper curr (x, t) = do
          n <- makeName "`T"
--          lift $ modify (\y -> (x, Scheme [] (FVar n)):y)
          (ty, as) <- local (\y -> (x, Scheme [] (FVar n)):(curr ++ y)) $ checkExpr t
          unification (FVar n) ty
          return $ as ++ [(x, Scheme [] (FVar n))]

smartSub :: [Decl] -> Subst -> [(VName, TScheme)] -> [(VName, TScheme)]
smartSub env sub as = map (helper env sub) as
  where helper env sub (x, Scheme vs t) =
          let t' = apply sub t
              a = toTScheme env t' in
          (x, a)

expp = Abs ["x", "y"] (Applica (Name "y") (Applica (Name "y") (Name "x")))
expp2 = Abs ["x"]  (Applica (Name "x") (Name "x"))

expp1 = Applica (Name "x") (Name "y")
testcase ex = do
           a <- runErrorT $ runReaderT (runReaderT (runStateT (runStateT (checkExpr ex) 0) []) []) []
           case a of
             Left e -> print $ disp e
             Right a -> do
                        print $ disp $ apply (snd a) ((fst . fst . fst) a)
                        print $ show $ (snd . fst . fst) a
                        print $ show $ snd a 

--runReader (runReaderT (fst (runStateT (fst $ ) []) []) []) []


--checkPat :: Prog -> TypeCxt (FType, TConstraints)

-- checkEq :: ([Prog], Prog) -> TypeCxt (FType, TConstraints)
-- checkEq (args, e) = do
--   (ts, cs) <- checkExprs args
--   (t, cs') <- checkExpr e
--   return $ (foldr arrow t ts, cs ++ cs')




      
      


-- typeInference :: Prog -> TypeCxt (FType, TConstraints)
-- typeInference (ProgPos _ p) = typeInference p
-- typeInference (Name x) = do
--   m <- lift get
--   case lookup x m of
--     Just a -> do
--       b <- freshInst a
--       return (b, [])
--     Nothing -> do
--       n <- get
--       modify (+1)
--       lift $ modify (\ y -> (x, (FVar $ "T" ++ show n)): y)
--       return (FVar $ "T"++ show n, [])


  






