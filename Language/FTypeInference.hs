{-# LANGUAGE NamedFieldPuns  #-}
module FTypeInference where
import Language.Syntax
import Language.PrettyPrint
import Language.Monad
import Text.PrettyPrint
import Control.Monad.Reader
import Control.Monad.Error
import Control.Monad.State
import Control.Monad.Identity
import qualified Data.Map as M


data TScheme = Scheme [VName] FType deriving (Show)

-- type TCMonad a =ReaderT [Decl] (StateT TypeEnv (ErrorT PCError IO)) a
-- data TypeEnv = TypeEnv{typeDef:: M.Map VName TScheme}
--              deriving Show

-- emptyTEnv :: TypeEnv
-- emptyTEnv = TypeEnv {typeDef = M.empty}

-- extendTypeDef :: VName -> TScheme -> TypeEnv -> TypeEnv
-- extendTypeDef v t e@(TypeEnv {typeDef}) = e{typeDef = M.insert v t typeDef}

def :: VName -> [Decl] -> Bool
def v ((DataDecl pos (Data name params cons) b):l) =
  if v == name then True else def v l
def v (x:l) = def v l
def v [] = False

toTScheme :: FType -> Reader [Decl] TScheme
toTScheme ft = do
  env <- ask
  return $ Scheme [ x | x <- freeVar ft, not (def x env)] ft

type TConstraints = [(FType, FType)]
type Subst = [(VName, FType)]
type TypeCxt a = StateT Int (StateT [(VName, TScheme)] (StateT [(VName, FType)] (ErrorT PCError IO))) a

tcError :: Disp d => d -> [(Doc, Doc)] -> TypeCxt a
tcError summary details = throwError (ErrMsg [ErrInfo (disp summary) details])

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

unification :: FType -> FType -> TypeCxt ()
unification t1 t2 = do
  subs <- lift $ lift get
  new <- unify (apply subs t1) (apply subs t2)
  lift $ lift $ put $ combine new subs
  
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
makeName :: VName -> TypeCxt VName
makeName name = do
  m <- get
  modify (+1)
  return $ name ++ show m

-- pattern included
checkExpr :: Prog -> TypeCxt FType
checkExpr (Name x) = do
  tdefs <- lift get
  case lookup x tdefs of
    Just sc -> do
      ft <- freshInst sc
      return ft
    Nothing -> do
      name <- makeName "`T"
      lift $ put $ (x, Scheme [] (FVar name)):tdefs
      return $ FVar name

checkExpr (Applica t1 t2) = do
  ty1 <- checkExpr t1
  ty2 <- checkExpr t2
  m <- makeName "`T"
  unification ty1 $ Arrow ty2 (FVar m)
  return $ FVar m
  
checkExpr (Abs xs t) = do
  ty <- checkExpr t
  ls <- mapM (\ x -> makeName "`T") xs
  let scs = map (\ y -> Scheme [] (FVar y)) ls
      tys = map (\ y -> FVar y) ls
      new = zip xs scs
  lift $ modify (\ y -> new ++ y)
  return $ foldr arrow ty tys

-- checkExpr (Let xs p) = do
--   mapM helper xs
--   where helper (x, p) = do
--           (t, cs) <- checkExpr p




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


  






