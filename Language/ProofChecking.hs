module Language.ProofChecking where
import Language.Syntax
import Language.Monad
import Language.Eval
import Control.Monad.State.Lazy
import qualified Data.Map as M
import qualified Data.Set as S
import Control.Monad.Reader
import Control.Monad.Error
compEType :: Meta -> Global EType
compEType (MVar x t) = do
  e <- ask
  case M.lookup x (gamma e) of
    Nothing -> throwError ("Can't find variable " ++ show x)
    Just a -> if a == t then return a
              else throwError ("type mismatch at " ++ show x)

compEType (Iota x Ind m) = do
  a <- local (extendGamma x Ind) (compEType m)
  if a == Ind then return Ind
    else return $ To Ind a

compEType (Iota x t m) = do
  a <- local (extendGamma x t) (compEType m)
  if a == Ind then throwError ("unexpect type Ind from"++ show m)
    else return $ To t a

compEType (Forall x t m) = local (extendGamma x t) (compEType m)

compEType (Imply m1 m2) = do
  a1 <- compEType m1
  a2 <- compEType m2
  if a1 == a2 then return a1
    else throwError ("EType mismatch at " ++ (show m1) ++ "and " ++ (show m2))

compEType (In m1 m2) = do
  a1 <- compEType m1
  a2 <- compEType m2
  case (a1, a2) of
    (Ind, Ind) -> return Ind
    (a3, To a c) ->
      if a == a3 then return c
      else throwError ("EType mismatch at " ++ (show m1) ++ "and " ++ (show m2))

ensureForm :: Meta -> Global ()
ensureForm m = do
  a <- compEType m
  unless (a == Form) $ throwError $ (show m) ++ " is not a well-formed formula"

compFormula :: Proof -> Global Meta
compFormula (PrVar v) = do
  e <- ask
  case M.lookup v (proofCxt e) of
    Just a -> 
      return $ snd a
    Nothing -> do 
      s <- get
      case lookup v (assumption s) of
        Just a1 -> return a1
        _ ->
          throwError $ "Can't find variable" ++ v

compFormula (Assume x f) = do
  ensureForm f
  e <- get
  put $ pushAssump x f e
  return f

compFormula (MP p1 p2) = do
 f1 <- compFormula p1
 ensureForm f1
 f2 <- compFormula p2
 ensureForm f2
 case f1 of
   Imply a1 a2 -> do
     if a1 == f2 then return a2
       else throwError "Modus Ponens Matching Error."
   _ -> throwError "Wrong use of Mondus Ponens"

compFormula (Discharge x p) = do
  e <- get
  if fst (head (assumption e)) == x then do
    f <- compFormula p
    put $ popAssump e
    let f2 = snd (head (assumption e)) in
      do
        ensureForm (Imply f2 f)
        return $ (Imply  f2 f)
    else throwError "Wrong use of implication introduction"

compFormula (Inst p m) = do
  f <- compFormula p
  ensureForm f
  t <- compEType m
  case f of
    Forall x t1 f1 ->
      if t == t1 then 
        let a = fst (runState (subst m (MVar x t1) f1) 0)
        in
         do
           ensureForm a
           return a
      else throwError $ "Type mismatch for "++(show m)
    _ -> throwError "Wrong use of Instantiation"

compFormula (UG x t p) = do
  e <- get
  if isFree x (assumption e)
    then throwError "Wrong use of universal generalization"
    else do
    f <- compFormula p
    ensureForm (Forall x t f)
    return $ (Forall x t f)

compFormula (Cmp p1) = do
  f1 <- compFormula p1
  ensureForm f1
  a <- comp f1
  ensureForm a
  return a

isFree :: VName -> [(VName, Meta)] -> Bool
isFree x m = not (null (filter (\ y ->  x `S.member` (fv (snd y))) m))

comp :: Meta -> Global Meta
comp (Forall x t f) = do
   f1 <- comp f
   return $ Forall x t f1

comp (Imply f1 f) = do
  a <- comp f1
  b <- comp f
  return $ Imply a b
  
comp m = reduce m

