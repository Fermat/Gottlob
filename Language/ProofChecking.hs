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
import Control.Monad.Identity

proofCheck :: ProofScripts -> Global ()

proofCheck ((n, (Assume x), f):l) = do
  wellDefined f
  wellFormed f
  insertAssumption x f
  proofCheck l

proofCheck ((n, p, f):l) = do
  f0 <- checkFormula p
  ensureEq f0 f
  wellFormed f
  
  proofCheck l

proofCheck [] = return ()

insertAssumption :: VName -> PreTerm -> Global ()
insertAssumption x f = do
  env <- lift get
  lift $ put $ pushAssump x f env
  return ()
  
wellDefined :: PreTerm -> Global ()
wellDefined t = do
  env <- get
  e <- lift get
  let l = S.toList $ fVar t 
      rs = map (\ x -> helper x env e) l
      fs = [c | c <- rs, fst c == False]
      ffs = map (\ x -> snd x) fs in
    if null ffs then return ()
    else throwError $ "undefine set variables: " ++ (show $ unwords ffs)
  where helper x env e =
          case M.lookup x (setDef env) of
            Just a -> (True, x)
            _ -> 
              case M.lookup x (localEType e) of
                Just b -> (True, x)
                _ -> (False, x)

wellFormed :: PreTerm -> Global (EType, Constraints, [(VName, EType)])
wellFormed f = do
  state <- get
  st <- lift get
  let s = runIdentity $ runStateT (runStateT (infer $ f) 0) ((map (\ x -> (fst x, (snd . snd) x)) (M.toList $ setDef state))++(M.toList $ localEType st))
      (t,c) = (fst. fst) s
      def = snd s
      res = solve c 0 in
      if isSolvable res 0 then
        return ((multiSub res t), res, (subDef res def)) 
      else throwError $ "Unsolvable formula or set definition for " ++ show f ++ show res

subDef :: Constraints -> [(VName, EType)] -> [(VName, EType)]
subDef res ((x,t):l) = (x, multiSub res t):(subDef res l)
subDef res [] = []
  

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
  unless (m1 == m2) $ throwError $ "In compatible preterm " ++ show m1 ++ "and " ++ show m2

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
          case M.lookup v (localProof s) of
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
      lift $ put $ popAssump e
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


-- checkProof :: ProofScripts -> Global String
-- checkProof ((n,p,f):xs) = do
--  a <- checkFormula p
--  e <- get
--  case p of
--    Assume _ _ -> checkProof xs
--    _ -> do
--      put $ extendLocalProof n p f e
--      checkProof xs

-- checkProof [] = do
--   put $ emptyPrfEnv
--   return $ "Passed proof check."


isFree :: VName -> [(VName, PreTerm)] -> Bool
isFree x m = not (null (filter (\ y ->  x `S.member` (fv (snd y))) m))

-- formula comprehension
comp :: PreTerm -> Global PreTerm
comp (Forall x f) = do
   f1 <- comp f
   return $ Forall x f1

comp (Imply f1 f) = do
  a <- comp f1
  b <- comp f
  return $ Imply a b

comp (In m1 (Iota x m)) = 
  return $ fst (runState (subst m1 (PVar x) m) 0)

comp (In m1 (PVar x)) = do
  e <- get
  let a = M.lookup x (setDef e)
  case a of
    Nothing -> return $ In m1 (PVar x)
    Just (s, t) -> return $ In m1 s

comp (SApp (Iota x m) m1) = 
  return $ fst (runState (subst m1 (PVar x) m) 0)

comp (SApp (PVar x) m1) = do
  e <- get
  let a = M.lookup x (setDef e)
  case a of
    Nothing -> return $ SApp (PVar x) m1
    Just (s, t) -> return $ SApp s m1

comp (TApp (Iota x m) m1) = 
  return $ fst (runState (subst m1 (PVar x) m) 0)

comp (TApp (PVar x) m1) = do
  e <- get
  let a = M.lookup x (setDef e)
  case a of
    Nothing -> return $ TApp (PVar x) m1
    Just (s, t) -> return $ TApp s m1

-- t :: (a :: C ) 
comp (SApp (SApp m3 m2) m1) = do
  a <- comp (SApp m3 m2)
  return $ SApp a m1

comp (TApp (SApp m3 m2) m1) = do
  a <- comp (SApp m3 m2)
  return $ TApp a m1

comp (SApp (TApp m3 m2) m1) = do
  a <- comp (TApp m3 m2)
  return $ SApp a m1

comp (TApp (TApp m3 m2) m1) = do
  a <- comp (TApp m3 m2)
  return $ TApp a m1

comp (Iota x m) = do
  a <- comp m
  return $ Iota x a
  
repeatComp :: PreTerm -> Global PreTerm
repeatComp m = do
  n <- comp m
  n1 <- comp n
  if n1 == n then return n
    else repeatComp n1

-- tr = (In (PVar "x") (In (PVar "y" ) (Iota "y"  (Iota "z2"  (In (PVar "y" Ind) (In (PVar "z2") (PVar "q" )))))))

-- compTest :: IO ()
-- compTest = do
--   b <- runErrorT $ runStateT (runReaderT (runGlobal (ensureForm tr )) emptyEnv) emptyPrfEnv
--   case b of
--     Left e -> putStrLn e
--     Right a -> do
--       c <- runErrorT $ runStateT (runReaderT (runGlobal (repeatComp tr )) emptyEnv) emptyPrfEnv 
--       case c of
--         Left e -> putStrLn e
--         Right a -> putStrLn $ show $ fst a

--tr1 = In (MVar "n" Ind) (In (MVar "U" (To Ind Form)) (MVar "Vec" (To (To Ind Form) (To Ind (To Ind Form)))))
-- compTest1 :: IO ()
-- compTest1 = do
--   b <- runErrorT $ runStateT (runReaderT (runGlobal (compEType tr1 )) emptyEnv) emptyPrfEnv
--   case b of
--     Left e -> putStrLn e
--     Right a ->
--       putStrLn $ show $ fst a
