module Language.ProofChecking where
import Language.Syntax
import Language.Monad
import Language.TypeInference
import Language.Eval
import Language.PrettyPrint

import Text.PrettyPrint
import Control.Monad.State.Lazy
import qualified Data.Map as M
import qualified Data.Set as S
import Control.Monad.Reader
import Control.Monad.Error
import Control.Monad.Identity

proofCheck :: ProofScripts -> Global ()
-- proofCheck ((n, (PPos pos p ), f):l) = 
--   proofCheck ((n,  p, f):l) `catchError` addProofErrorPos pos p
  
proofCheck ((n, (Assume x), f):l) = do
  wellDefined f
  wellFormed f
  insertAssumption x f
--  emit $ "checked assumption"
  proofCheck l

proofCheck ((n, p, f):l) = do
--  emit $ "begin to check proof " ++ show p
  f0 <- checkFormula p
  sameFormula f0 f
  wellFormed f
  insertPrVar n p f
--  emit $ "checked non-assump"
  proofCheck l

proofCheck [] = return ()

insertAssumption :: VName -> PreTerm -> Global ()
insertAssumption x f = do
  env <- lift get
  lift $ put $ pushAssump x f env
  return ()

insertPrVar :: VName -> Proof -> PreTerm -> Global ()
insertPrVar x p f = do
  env <- lift get
  lift $ put $ extendLocalProof x p f env
  return ()

wellDefined :: PreTerm -> Global ()
wellDefined (Pos pos p) =
  wellDefined p `catchError` addPreErrorPos pos p
wellDefined t = do
  env <- get
  e <- lift get
  let l = S.toList $ fVar t 
      rs = map (\ x -> helper x env e) l
      fs = [c | c <- rs, fst c == False]
      ffs = map (\ x -> snd x) fs in
    if null ffs then return ()
    else die $ "Undefined set variables: " <++> (unwords ffs)
  where helper x env e =
          case M.lookup x (setDef env) of
            Just a -> (True, x)
            _ -> 
              case M.lookup x (localEType e) of
                Just b -> (True, x)
                _ -> (False, x)

wellFormed :: PreTerm -> Global (EType, Constraints, [(VName, EType)])
wellFormed (Pos pos f) =
  wellFormed f `catchError` addPreErrorPos pos f
wellFormed f = do
  state <- get
  st <- lift get
  let s = runIdentity $ runStateT (runStateT (infer $ f) 0) ((map (\ x -> (fst x, (snd . snd) x)) (M.toList $ setDef state))++(M.toList $ localEType st))
      (t,c) = (fst. fst) s
      def = snd s
      res = solve c 0 in
      if isSolvable res 0 then
        return ((multiSub res t), res, (subDef res def)) 
      else pcError "Ill-formed formula or set definition."
           [(disp "Unsolvable constraints", disp res)]

subDef :: Constraints -> [(VName, EType)] -> [(VName, EType)]
subDef res ((x,t):l) = (x, multiSub res t):(subDef res l)
subDef res [] = []
  

ensureForm :: PreTerm -> Global (EType, Constraints, [(VName, EType)])
ensureForm (Pos pos f) =
  ensureForm f `catchError` addPreErrorPos pos f
ensureForm m = do
  (a, b, c) <- wellFormed m
  unless (a == Form) $ die " Ill-formed formula."
  return (a,b,c)
  
ensureTerm :: PreTerm -> Global ()
ensureTerm m = do
  unless (isTerm m) $ die $ m <++> " is not a lambda term"

-- ensureEq :: (Eq a, Show a) => a -> a -> Global ()
-- ensureEq m1 m2 = 
--   unless (m1 == m2) $ throwError $ "In compatible preterm " ++ show m1 ++ "and " ++ show m2

checkFormula :: Proof -> Global PreTerm

checkFormula (PPos pos p) =
  checkFormula p `catchError` addProofErrorPos pos p

checkFormula (PrVar v)  = do
--  emit $ "entering var case"
  e <- get
  case M.lookup v (proofCxt e) of
    Just a -> return $ snd a
    Nothing -> do 
      s <- lift get
      case lookup v (assumption s) of
        Just a1 -> 
--          emit $ "var found in assumption" ++ show a1
          return a1
        _ ->
          case M.lookup v (localProof s) of
            Just a2 -> return $ snd a2
            _ -> 
              die $ "Can't find proof variable" <++> v

checkFormula (MP p1 p2) = do
 f1 <- checkFormula p1 
-- ensureForm f1
 f2 <- checkFormula p2
-- ensureForm f2
 case f1 of
   Imply a1 a2 -> do
     sameFormula a1 f2 
     ensureForm a2
     return a2
   _ -> pcError "Wrong use of mondus ponens."
        [(disp "At the proof", disp p1)]

checkFormula (Discharge x p) = do
  e <- lift get
  let h = head (assumption e) in
    if fst h == x then do
      f <- checkFormula p
      ensureForm (Imply (snd h) f)
      lift $ put $ popAssump e
      return $ (Imply (snd h) f)
    else pcError "Wrong use of implication introduction, can't not discarge the assumption."
         [(disp "At the variable", disp x)]

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
    _ -> pcError "Wrong use of Instantiation."
         [(disp "At the proof", disp p)]

checkFormula (UG x p)  = do
  e <- lift get
  if isFree x (assumption e)
    then pcError "Wrong use of universal generalization."
         [(disp "generalized variable" <+> disp x, disp "appears in the assumptions")]
    else do
    f <- checkFormula p
    ensureForm (Forall x f)
    return $ (Forall x f)

checkFormula (Cmp p1) = do
  f1 <- checkFormula p1
--  emit $ "going in with formula" ++ show f1
  a <- repeatComp $ erased f1
--  emit $ "done with comprehension"
--  ensureForm a
  return a

checkFormula (InvCmp p1 m1) = do
  f1 <- checkFormula p1
  a <- repeatComp $ erased m1
  sameFormula a f1
  return m1

checkFormula (Beta p1) = do
  f1 <- checkFormula p1
  case f1 of
    In t m -> do
      ensureTerm t
      t1 <- reduce $ erased t
      return $ In t1 m
    _ -> pcError "beta must be use on formula of the form: <term> :: <Set>"
         [(disp "of the proof", disp p1), (disp "In the formula", disp f1)]

checkFormula (InvBeta p1 form) = do
  f1 <- checkFormula p1
  case form of
    In t m -> do
      ensureTerm t
      t1 <- reduce $ erased t
      sameFormula (In t1 m) f1
      return $ In t1 m
    _ -> pcError "invbeta must be use on formula of the form: <term> :: <Set>"
         [(disp "In the formula", disp form)]

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
-- erased positions
erased :: PreTerm -> PreTerm
erased (Pos p t) = erased t
erased (PVar x) = PVar x
erased (Forall x p) = Forall x (erased p)
erased (Imply p1 p2) = Imply (erased p1) (erased p2)
erased (Iota x p) = Iota x (erased p)
erased (In p1 p2) = In (erased p1) (erased p2)
erased (SApp p1 p2) = SApp (erased p1) (erased p2)
erased (TApp p1 p2) = TApp (erased p1) (erased p2)
erased (App p1 p2) = App (erased p1) (erased p2)
erased (Lambda x p) = Lambda x (erased p)

isFree :: VName -> [(VName, PreTerm)] -> Bool
isFree x m = not (null (filter (\ y ->  x `S.member` (fv (snd y))) m))

-- formula comprehension
-- severe bug found, need to fix
comp :: PreTerm -> S.Set VName  -> Global PreTerm
comp (Forall x f) s = do
   f1 <- comp f s
   return $ Forall x f1

comp (Imply f1 f) s = do
  a <- comp f1 s
  b <- comp f s
  return $ Imply a b

comp (In m1 (Iota x m)) s = 
  return $ fst (runState (subst m1 (PVar x) m) 0)

comp (In m1 (PVar x)) s = 
  if x `S.member` s then 
    do
      e <- get
      let a = M.lookup x (setDef e)
      case a of
        Nothing -> die $ "Impossible situation during comprhension."
        Just (s1, t) -> return $ In m1 s1
  else return $ In m1 (PVar x)

comp (SApp (Iota x m) m1) s = 
  return $ fst (runState (subst m1 (PVar x) m) 0)

comp (SApp (PVar x) m1) s =
  if x `S.member` s then 
    do
      e <- get
      let a = M.lookup x (setDef e)
      case a of
        Nothing -> die $ "Impossible situation during comprhension."
        Just (s1, t) -> return $ SApp s1 m1
  else return $ SApp (PVar x) m1
       
comp (TApp (Iota x m) m1) s = 
  return $ fst (runState (subst m1 (PVar x) m) 0)

comp (TApp (PVar x) m1) s =
  if x `S.member` s then 
    do
      e <- get
      let a = M.lookup x (setDef e)
      case a of
        Nothing -> die $ "Impossible situation during comprhension."
        Just (s1, t) -> return $ TApp s1 m1
  else return $ TApp (PVar x) m1
-- t :: (a :: C ) 
comp (SApp (SApp m3 m2) m1) s = do
  a <- comp (SApp m3 m2) s
  return $ SApp a m1

comp (TApp (SApp m3 m2) m1) s = do
  a <- comp (SApp m3 m2) s
  return $ TApp a m1

comp (SApp (TApp m3 m2) m1) s = do
  a <- comp (TApp m3 m2) s
  return $ SApp a m1

comp (TApp (TApp m3 m2) m1) s = do
  a <- comp (TApp m3 m2) s
  return $ TApp a m1

comp (Iota x m) s = do
  a <- comp m s
  return $ Iota x a

comp (PVar x) s = 
  if x `S.member` s then 
    do
      e <- get
      let a = M.lookup x (setDef e)
      case a of
        Nothing -> return $ PVar x
        Just (s1, t) -> return $ s1
  else return $ PVar x


repeatComp :: PreTerm -> Global PreTerm
repeatComp m = do
  n <- comp m (fv m)
--  emit $ "single comp, get " ++ show n
  n1 <- comp n (fv n)
  -- emit $ "1next comp, get " ++ show n1
  -- n2 <- comp n1
  -- emit $ "2next comp, get " ++ show n2
  -- n3 <- comp n2
  -- emit $ "3next comp, get " ++ show n3
  if n == n1 then return n
    else 
  --  throwError "So n2 and n3 are not eq. Stop now"
    repeatComp n1

tr = In (PVar "m") (Iota "x" (Forall "Nat" (Imply (In (PVar "z") (PVar "Nat")) (Imply (In (PVar "s") (Iota "f" (Forall "x" (Imply (In (PVar "x") (PVar "Nat")) (In (App (PVar "f") (PVar "x")) (PVar "Nat")))))) (In (PVar "x") (PVar "Nat"))))))

tr1 = Forall "C" (Imply (In (PVar "z") (PVar "C")) (Imply (Forall "y" (Imply (In (PVar "y") (PVar "C")) (In (App (PVar "s") (PVar "y")) (PVar "C")))) (In (PVar "m") (PVar "C"))))

tr2 = Forall "Nat" (Imply (In (PVar "z") (PVar "Nat")) (Imply (Forall "x" (Imply (In (PVar "x") (PVar "Nat")) (In (App (PVar "s") (PVar "x")) (PVar "Nat")))) (In (PVar "m") (PVar "Nat"))))

compTest :: IO ()
compTest = do
  c <- runErrorT $ runStateT (runStateT (repeatComp tr) emptyEnv) emptyPrfEnv 
  case c of
    Left e -> print $ disp e
    Right a -> print $ disp ((fst . fst) a)

--tr1 = In (MVar "n" Ind) (In (MVar "U" (To Ind Form)) (MVar "Vec" (To (To Ind Form) (To Ind (To Ind Form)))))
-- compTest1 :: IO ()
-- compTest1 = do
--   b <- runErrorT $ runStateT (runReaderT (runGlobal (compEType tr1 )) emptyEnv) emptyPrfEnv
--   case b of
--     Left e -> putStrLn e
--     Right a ->
--       putStrLn $ show $ fst a
