{-# LANGUAGE NamedFieldPuns  #-}
module FTypeInference where
import Language.Syntax
import Language.PrettyPrint
import Language.Monad
import Control.Monad.Reader
import Control.Monad.Error
import Control.Monad.State
import Control.Monad.Identity
import qualified Data.Map as M


data TScheme = Scheme [VName] FType deriving (Show)

type TCMonad a =ReaderT [Decl] (StateT TypeEnv (ErrorT PCError IO)) a
data TypeEnv = TypeEnv{typeDef:: M.Map VName TScheme}
             deriving Show

emptyTEnv :: TypeEnv
emptyTEnv = TypeEnv {typeDef = M.empty}

extendTypeDef :: VName -> TScheme -> TypeEnv -> TypeEnv
extendTypeDef v t e@(TypeEnv {typeDef}) = e{typeDef = M.insert v t typeDef}


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
type TypeCxt a = StateT Int (StateT [(VName, TScheme)] Identity) a

-- unification

unify :: FType -> FType -> 
arrow a b = Arrow a b

apply subs (FVar x) =
  case lookup x subs of
    Just x1 -> FVar x1
    Nothing -> FVar x
apply subs (Arrow f1 f2) =
  let a1 = apply subs f1
      a2 = apply subs f2 in
  Arrow a1 a2
apply subs (FCons c args) =
  case lookup c subs of
    Just x1 -> FCons x1 (map (helper subs) args)
    Nothing -> FCons c (map (helper subs) args)
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
   let substs = zip xs newVars in
    return $ apply substs t
makeName :: VName -> TypeCxt VName
makeName name = do
  m <- get
  modify (+1)
  return $ name ++ show m

-- pattern included
checkExpr :: Prog -> TypeCxt (FType, TConstraints)
checkExpr (Name x) = do
  tdefs <- lift get
  case lookup x tdefs of
    Just sc -> do
      ft <- freshInst sc
      return (ft, [])
    Nothing -> do
      name <- makeName "`T"
      lift $ put $ (x, Scheme [] (FVar name)):tdefs
      return (FVar name, [])

checkExpr (Applica t1 t2) = do
  (ty1, cs1) <- checkExpr t1
  (ty2, cs2) <- checkExpr t2
  m <- makeName "`T"
  return (FVar m,  (ty1, Arrow ty2 (FVar m)):(cs1 ++ cs2))
  
checkExpr (Abs xs t) = do
  (ty, cs) <- checkExpr t
  ls <- mapM (\ x -> makeName "`T") xs
  let scs = map (\ y -> Scheme [] (FVar y)) ls
      tys = map (\ y -> FVar y) ls
      new = zip xs scs
  lift $ modify (\ y -> new ++ y)
  return (foldr arrow ty tys, cs)

checkExpr (Let xs p) = do
  mapM helper xs
  where helper (x, p) = do
          (t, cs) <- checkExpr p
          
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


  






