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
    Nothing -> return t
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

ensureTerm :: Meta -> Global ()
ensureTerm m = do
  a <- compEType m
  unless (a == Ind) $ throwError $ (show m) ++ " is not a lambda term"

ensureEq :: (Eq a, Show a) => a -> a -> Global ()
ensureEq m1 m2 = 
  unless (m1 == m2) $ throwError $ "In compatible meta term " ++ show m1 ++ "and " ++ show m2

checkFormula :: Proof -> Global Meta
checkFormula (PrVar v)  = do
  e <- ask
  case M.lookup v (proofCxt e) of
    Just a -> return $ snd a
    Nothing -> do 
      s <- get
      case lookup v (assumption s) of
        Just a1 ->
          return a1
        _ -> 
          throwError $ "Can't find variable" ++ v

checkFormula (Assume x m) = do
  ensureForm m
  e <- get
  put $ pushAssump x m e
  return m

checkFormula (MP p1 p2 m) = do
 f1 <- checkFormula p1 
 ensureForm f1
 f2 <- checkFormula p2
 ensureForm f2
 case f1 of
   Imply a1 a2 -> do
     if a1 == f2 then do
       ensureEq a2 m
       return a2
       else throwError "Modus Ponens Matching Error."
   _ -> throwError "Wrong use of Mondus Ponens"


checkFormula (Discharge x p m) = do
  e <- get
  if fst (head (assumption e)) == x then do
    f <- checkFormula p
    put $ popAssump e
    let f2 = snd (head (assumption e)) in
      do
        ensureForm (Imply f2 f)
        ensureEq (Imply f2 f) m
        return $ (Imply f2 f)
    else throwError "Wrong use of implication introduction"

checkFormula (Inst p m form) = do
  f <- checkFormula p
  ensureForm f
  t <- compEType m
  case f of
    Forall x t1 f1 ->
      if t == t1 then 
        let a = fst (runState (subst m (MVar x t1) f1) 0)
        in
         do
           ensureForm a
           ensureEq a form
           return a
      else throwError $ "Type mismatch for "++(show m)
    _ -> throwError "Wrong use of Instantiation"

checkFormula (UG x t p m) = do
  e <- get
  if isFree x (assumption e)
    then throwError "Wrong use of universal generalization"
    else do
    f <- checkFormula p
    ensureForm (Forall x t f)
    ensureEq (Forall x t f) m
    return $ (Forall x t f)

checkFormula (Cmp p1 m) = do
  f1 <- checkFormula p1
  ensureForm f1
  a <- repeatComp f1
  ensureForm a
  ensureEq a m
  return a

checkFormula (InvCmp p1 m1) = do
  f1 <- checkFormula p1
  ensureForm f1
  a <- repeatComp m1
  ensureForm a
  ensureEq a f1
  return m1

checkFormula (Beta p1 form) = do
  f1 <- checkFormula p1
  ensureForm f1
  case f1 of
    In t m -> do
      ensureTerm t
      t1 <- reduce t
      ensureForm $ In t1 m
      ensureEq (In t1 m) form
      return $ In t1 m
    _ -> throwError "This form of extensionality is not supported"

checkFormula (InvBeta p1 form) = do
  f1 <- checkFormula p1
  ensureForm f1
  case form of
    In t m -> do
      ensureTerm t
      t1 <- reduce t
      ensureForm $ In t1 m
      ensureEq (In t1 m) f1
      return $ In t1 m
    _ -> throwError "This form of extensionality is not supported"

checkProof :: ProofScripts -> Global String
checkProof ((n,p,f):xs) = do
 a <- checkFormula p
 e <- get
 case p of
   Assume _ _ -> checkProof xs
   _ -> do
     put $ extendLocalProof n p f e
     checkProof xs

checkProof [] = do
  put $ emptyPrfEnv
  return $ "Passed proof check."


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

comp (In m1 (Iota x t m)) = do
  a <- compEType (In m1 (Iota x t m))
  case a of
    Ind -> return $ In m1 (Iota x t m)
    _ -> return $ fst (runState (subst m1 (MVar x t) m) 0)

comp (In m1 (MVar x t)) = do
  e <- ask
  let a = M.lookup x (def e)
  case a of
    Nothing -> return $ In m1 (MVar x t)
    Just (et, t) -> return $ In m1 t
  
comp (In m1 (In m2 m3)) = do
  a <- comp (In m2 m3)
  return $ In m1 a

comp (Iota x t m) = do
  a <- comp m
  return $ Iota x t a
  
repeatComp :: Meta -> Global Meta
repeatComp m = do
  n <- comp m
  n1 <- comp n
  if n1 == n then return n
    else repeatComp n1

tr = (In (MVar "x" Ind) (In (MVar "y" Ind) (Iota "y" Ind (Iota "z2" Ind (In (MVar "y" Ind) (In (MVar "z2" Ind) (MVar "q" (To Ind (To Ind Form)))))))))

compTest :: IO ()
compTest = do
  b <- runErrorT $ runStateT (runReaderT (runGlobal (ensureForm tr )) emptyEnv) emptyPrfEnv
  case b of
    Left e -> putStrLn e
    Right a -> do
      c <- runErrorT $ runStateT (runReaderT (runGlobal (repeatComp tr )) emptyEnv) emptyPrfEnv 
      case c of
        Left e -> putStrLn e
        Right a -> putStrLn $ show $ fst a

tr1 = In (MVar "n" Ind) (In (MVar "U" (To Ind Form)) (MVar "Vec" (To (To Ind Form) (To Ind (To Ind Form)))))
compTest1 :: IO ()
compTest1 = do
  b <- runErrorT $ runStateT (runReaderT (runGlobal (compEType tr1 )) emptyEnv) emptyPrfEnv
  case b of
    Left e -> putStrLn e
    Right a ->
      putStrLn $ show $ fst a
