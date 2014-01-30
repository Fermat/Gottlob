module Language.ProofChecking where
import Language.Syntax
import Language.Monad
import Language.TypeInference
import Language.Eval
import Control.Monad.State.Lazy
import qualified Data.Map as M
import qualified Data.Set as S
import Control.Monad.Reader
import Control.Monad.Error

proofCheck :: ProofScripts -> [(VName, EType)] -> Global ()
proofCheck [] = return ()
proofCheck ((n, (Assume x), f):l) = do
  wellDefined f
  insertAssumption x f
  proofCheck l

proofCheck ((n, p, f):l) = do
  f0 <- checkFormula p
  ensureEq f0 f
  wellFormed f 
  proofCheck l
  
wellDefined :: PreTerm -> Global ()
wellDefined t = do
  env <- get
  let l = S.toList $ fVar t 
      rs = map (\ x -> helper x env) l
      fs = [c | c <- rs, fst c == False]
      ffs = map (\ x -> snd x) fs in
    if null ffs then return ()
    else throwError $ "undefine set variables: " ++ (show $ unwords ffs)
  where helper x env =
          case M.lookup x (setDef env) of
            Just a -> (True, x)
            _ -> (False, x)

wellFormed :: PreTerm -> Global (EType, Constraints, [(VName, EType)])
wellFormed f = do
  state <- get
  let s = runIdentity $ runStateT (runStateT (infer $ f) 0) (map (\ x -> (fst x, (snd . snd) x)) (M.toList $ setDef state))
      (t,c) = (fst. fst) s
      def = snd s
      res = solve c 0 in
      if isSolvable res 0 then
        return ((multiSub res t), res, def)
      else throwError $ "Unsolvable formula or set definition for " ++ show f

ensureForm :: PreTerm -> Global (EType, Constraints, [(VName, EType)])
ensureForm m = do
  (a, b, c) <- wellFormed m
  unless (a == Form) $ throwError $ (show m) ++ " is not a well-formed formula"
  return (a,b,c)
  
ensureTerm :: PreTerm -> Global ()
ensureTerm m = do
  unless (isTerm m) $ throwError $ (show m) ++ " is not a lambda term"

ensureEq :: (Eq a, Show a) => a -> a -> Global ()
ensureEq m1 m2 = 
  unless (m1 == m2) $ throwError $ "In compatible meta term " ++ show m1 ++ "and " ++ show m2

checkFormula :: Proof -> Global PreTerm
checkFormula (PrVar v)  = do
  e <- get
  case M.lookup v (proofCxt e) of
    Just a -> return $ snd a
    Nothing -> do 
      s <- lift get
      case lookup v (assumption s) of
        Just a1 ->
          return a1
        _ ->
          case lookup v (localProof s) of
            Just a2 -> return $ snd a2
            _ -> 
              throwError $ "Can't find variable" ++ v

checkFormula (MP p1 p2) = do
 f1 <- checkFormula p1 
-- ensureForm f1
 f2 <- checkFormula p2
-- ensureForm f2
 case f1 of
   Imply a1 a2 -> do
     if a1 == f2 then do
       ensureForm a2
       return a2
       else throwError "Modus Ponens Matching Error."
   _ -> throwError "Wrong use of Mondus Ponens"

checkFormula (Discharge x p) = do
  e <- lift get
  let h = head (assumption e) in
    if fst h == x then do
      f <- checkFormula p
      ensureForm (Imply (snd h) f)
      put $ popAssump e
      return $ (Imply (snd h) f)
    else throwError "Wrong use of implication introduction"

checkFormula (Inst p m) = do
  f <- checkFormula p
  case f of
    Forall x f1 ->
      let a = fst (runState (subst m (PVar x) f1) 0)
        in
         do
           ensureForm a
           return a
--      else throwError $ "Type mismatch for "++(show m)
    _ -> throwError "Wrong use of Instantiation"

checkFormula (UG x p)  = do
  e <- lift get
  if isFree x (assumption e)
    then throwError "Wrong use of universal generalization"
    else do
    f <- checkFormula p
    ensureForm (Forall x f)
    return $ (Forall x f)

checkFormula (Cmp p1) = do
  f1 <- checkFormula p1
  a <- repeatComp f1
  ensureForm a
  return a

checkFormula (InvCmp p1 m1) = do
  f1 <- checkFormula p1
  a <- repeatComp m1
  ensureEq a f1
  return m1

checkFormula (Beta p1) = do
  f1 <- checkFormula p1
  case f1 of
    In t m -> do
      ensureTerm t
      t1 <- reduce t
      return $ In t1 m
    _ -> throwError "This form of extensionality is not supported"

checkFormula (InvBeta p1 form) = do
  f1 <- checkFormula p1
  case form of
    In t m -> do
      ensureTerm t
      t1 <- reduce t
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
