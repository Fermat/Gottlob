module Language.ProofChecking
       (proofCheck, wellDefined, wellFormed,
        ensureForm, erased) where
import Language.Syntax
import Language.Monad
import Language.TypeInference
import Language.Eval
import Language.PrettyPrint

import Text.PrettyPrint

import Control.Monad.State.Lazy
import Control.Monad.Reader
import Control.Monad.Error
import Control.Monad.Identity

import qualified Data.Map as M
import qualified Data.Set as S
import Data.Char

proofCheck :: ProofScripts -> Global ()
-- proofCheck ((n, (PPos pos p ), f):l) f1 = 
--   proofCheck ((n,  p, f):l) `catchError` addProofErrorPos pos p
  
proofCheck ((n, Left (Assume x), Just f):l) = do
--  wellDefined f
  wellFormed f
  insertAssumption x f
--  emit $ "checked assumption"
  proofCheck l

proofCheck ((n, Right p, Just f):l) = do
  emit $ "begin to check proof " <++> disp p
  wellFormed f
  p1 <- simp p --  normalize a proof
--  emit $ "begin to check simp proof " <++> disp p1
  f0 <- checkFormula p1

--  emit $ disp f0 <+> text "?=" <+> disp f
  sameFormula f0 f -- this can be handle by passing to checkformula
--  emit $ "pass same"
  insertPrVar n p1 (erased f)
--  emit $ "checked non-assump"
  proofCheck l

proofCheck ((n, Right p, Nothing):l) = do
  emit $ "begin to check proof " <++> disp p
--  emit $ "a list of fv " ++ show (fv p)
  p1 <- simp p  --  normalize a proof
  f0 <- checkFormula p1
  emit $ text "Infered formula:" <+> disp f0 <+> text "for proof" <+> disp n
  insertPrVar n p1 (erased f0)
  proofCheck l

proofCheck [] = return ()

insertAssumption :: VName -> PreTerm -> Global ()
insertAssumption x f = do
  env <- lift get
  lift $ put $ pushAssump x f env
  return ()

insertPrVar :: VName -> PreTerm -> PreTerm -> Global ()
insertPrVar x p f = do
  env <- lift get
  lift $ put $ extendLocalProof x p f env
  return ()

-- Check if the 'free' set variable in a preterm is
-- previously defined.
wellDefined :: PreTerm -> Global ()
wellDefined (Pos pos p) = wellDefined p `catchError` addPreErrorPos pos p
wellDefined t = do
  env <- get
  let l = S.toList $ fVar t 
      rs = map (\ x -> helper x env) l
      fs = [snd c | c <- rs, fst c == False] in
    if null fs then return ()
    else die $ "Undefined set variables: " <++> (hsep $ punctuate comma (map text fs))
  where helper x env = case M.lookup x (setDef env) of
                            Just a -> (True, x)
                            _ -> (False, x)

wellFormed :: PreTerm -> Global (EType, Constraints, [(VName, EType)])
wellFormed (Pos pos f) =
  wellFormed f `catchError` addPreErrorPos pos f
wellFormed f = do
  state <- get
  st <- lift get  
  let glAnt = map (\ (v, (_, etype)) -> (v, etype)) (M.toList $ setDef state)
      env = glAnt ++ (M.toList $ localEType st)
      (t,c,def) = runInference f env
      res = runSolve c in
      if isSolvable res then
        return ((multiSub res t), res, (subDef res def)) 
      else pcError "Ill-formed formula or set definition."
           [(disp "Unsolvable constraints", disp res)]

subDef :: Constraints -> [(VName, EType)] -> [(VName, EType)]
subDef res l = map (\ (x, t) -> (x, multiSub res t)) l

ensureForm :: PreTerm -> Global (EType, Constraints, [(VName, EType)])
ensureForm (Pos pos f) = ensureForm f `catchError` addPreErrorPos pos f
ensureForm m = do
  (a, b, c) <- wellFormed m
  unless (a == Form) $ die "Ill-formed formula."
  return (a,b,c)
  
checkFormula :: PreTerm -> Global PreTerm
checkFormula (Pos pos p) = checkFormula p -- `catchError` addProofErrorPos pos p
checkFormula (PVar v)  = do
  e <- get
  loc <- ask
  case M.lookup v (proofCxt e) of
    Just a -> return $ snd a
    Nothing -> do 
      s <- lift get
      case lookup v loc of
        Just a3 -> return a3
        _ -> 
          case lookup v (assumption s) of
            Just a1 -> return a1
            _ -> case M.lookup v (localProof s) of
                    Just a2 -> return $ snd a2
                    _ -> die $ "Can't find proof variable" <++> v

checkFormula (MP p1 p2) = do
 f1 <- checkFormula p1 
 f2 <- checkFormula p2
 case down f1 of
   Imply a1 a2 -> do
     sameFormula f2 a1
     ensureForm a2
     return a2
   _ -> pcError "Wrong use of mondus ponens."
        [(disp "At the proof", disp p1)]

checkFormula (Discharge x Nothing p) = do
  e <- lift get
  case lookup x (assumption e) of --  (y, f1)
    Just f1 -> do
      f <- local (\ l -> (x, f1):l) (checkFormula p)
      a <- lift $ get
      if fst (head $ assumption a) == x
        then
        do
--          emit $ text "discharging " <+> disp x
          lift $ put $ popAssump a
         
--          emit $ text "current head assumption" <+> (disp $ fst (head $ assumption a))
          ensureForm (Imply f1 f)
          return $ (Imply f1 f)
        else pcError "Wrong use of implication introduction, can't not discharge the assumption."
             [(disp "At the variable", disp x)]
    Nothing -> die $ disp x <+> text "is not in assumptions."

checkFormula (Discharge x (Just f1) p) = do
  wellFormed f1
  f <- local (\l -> (x, f1):l) (checkFormula p)
  ensureForm (Imply f1 f)
  e <- lift get
--  lift $ put $ popAssump e
  return $ (Imply f1 f)
  
checkFormula (Inst p m) = do
  f <- checkFormula p
  case down f of
    Forall x f1 ->
      let a = runSubst m (PVar x) f1 in
      ensureForm a >> return a
    _ -> pcError "Wrong use of Instantiation."
         [(disp "At the proof", disp p),
          (disp "With the formula", disp f)]

checkFormula (UG x p)  = do
  f <- checkFormula p
  e <- lift get
  if isFree x (assumption e)
    then pcError "Wrong use of universal generalization."
         [(disp "generalized variable" <+> disp x, disp "appears in the assumptions")]
    else do
    ensureForm (Forall x f)
    return $ (Forall x f)

checkFormula (Cmp p1) = do
  f1 <- checkFormula p1
  a <- repeatComp $ erased f1
  ensureForm a
  return a

checkFormula (InvCmp p1 m1) = do
  ensureForm m1
  f1 <- checkFormula p1
  a <- repeatComp $ erased m1
  sameFormula a f1
  return m1

checkFormula (Beta p1) = do
  f1 <- checkFormula p1
  case down f1 of
    In t m -> do
      t1 <- reduce $ erased t
      ensureForm $ In t1 m
      return $ In t1 m
    _ -> pcError "beta must be use on formula of the form: <term> :: <Set>"
         [(disp "of the proof", disp p1), (disp "In the formula", disp f1)]

checkFormula (InvBeta p1 form) = do
  ensureForm form
  f1 <- checkFormula p1
  case down form of
    In t m -> do
      t1 <- reduce $ erased t
      sameFormula (In t1 m) f1
--      emit $ disp (In t1 m) <+> disp f1
      return form
    _ -> pcError "invbeta must be use on formula of the form: <term> :: <Set>"
         [(disp "In the formula", disp form)]

checkFormula p = pcError "Un-normal proof"
         [(disp "The proof", disp p)]
         
down :: PreTerm -> PreTerm
down (Pos _ t) = down t
down t = t
-- erased all the positions
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


comp :: PreTerm -> S.Set VName  -> Global PreTerm
comp (Pos pos p) s = comp p s
comp (Forall x f) s = comp f s >>= \ f1 -> return $ Forall x f1
comp (Imply f1 f) s = do
  a <- comp f1 s
  b <- comp f s
  return $ Imply a b

comp (In m1 (Iota x m)) s = return $ runSubst m1 (PVar x) m

comp (In m1 (PVar x)) s = 
  if x `S.member` s then do
    e <- get
    case M.lookup x (setDef e) of
      Nothing -> return $ In m1 (PVar x)
      Just (s1, t) -> return $ In m1 s1
  else return $ In m1 (PVar x)
comp (In m1 (SApp s1 s2)) s = do
  r <- comp (SApp s1 s2) s
  return $ In m1 r
  
comp (SApp (Iota x m) m1) s = return $ runSubst m1 (PVar x) m

comp (SApp (PVar x) m1) s =
  if x `S.member` s then do
    e <- get
    case M.lookup x (setDef e) of
      Nothing -> return $ SApp (PVar x) m1
      Just (s1, t) -> return $ SApp s1 m1
  else return $ SApp (PVar x) m1
       
comp (TApp (Iota x m) m1) s = return $ runSubst m1 (PVar x) m

comp (TApp (PVar x) m1) s =
  if x `S.member` s then do
    e <- get
    case M.lookup x (setDef e) of
      Nothing -> return $ TApp (PVar x) m1
      Just (s1, t) -> return $ TApp s1 m1
  else return $ TApp (PVar x) m1
-- t :: (a :: C ) 
comp (SApp (SApp m3 m2) m1) s = 
  comp (SApp m3 m2) s >>= \ a-> return $ SApp a m1

comp (TApp (SApp m3 m2) m1) s = 
   comp (SApp m3 m2) s >>= \ a -> return $ TApp a m1

comp (SApp (TApp m3 m2) m1) s =
  comp (TApp m3 m2) s >>= \ a -> return $ SApp a m1

comp (TApp (TApp m3 m2) m1) s = 
  comp (TApp m3 m2) s >>= \ a -> return $ TApp a m1

comp (Iota x m) s = comp m s >>= \ a -> return $ Iota x a

comp (PVar x) s = 
  if x `S.member` s then do
    e <- get
    case  M.lookup x (setDef e) of
      Nothing -> return $ PVar x
      Just (s1, t) -> return $ s1
  else return $ PVar x

comp n s = die $ text "unhandle case in comp" <++> disp n
repeatComp :: PreTerm -> Global PreTerm
repeatComp m = do
  n <- comp m (fv m)
--  emit $ show n
  n1 <- comp n (fv n)
--  emit $ show n1
  if n == n1 then return n else repeatComp n1


-- tr = In (PVar "m") (Iota "x" (Forall "Nat" (Imply (In (PVar "z") (PVar "Nat")) (Imply (In (PVar "s") (Iota "f" (Forall "x" (Imply (In (PVar "x") (PVar "Nat")) (In (App (PVar "f") (PVar "x")) (PVar "Nat")))))) (In (PVar "x") (PVar "Nat"))))))

-- tr1 = Forall "C" (Imply (In (PVar "z") (PVar "C")) (Imply (Forall "y" (Imply (In (PVar "y") (PVar "C")) (In (App (PVar "s") (PVar "y")) (PVar "C")))) (In (PVar "m") (PVar "C"))))

-- tr2 = Forall "Nat" (Imply (In (PVar "z") (PVar "Nat")) (Imply (Forall "x" (Imply (In (PVar "x") (PVar "Nat")) (In (App (PVar "s") (PVar "x")) (PVar "Nat")))) (In (PVar "m") (PVar "Nat"))))

-- compTest :: IO ()
-- compTest = do
--   c <- runErrorT $ runStateT (runStateT (repeatComp tr) emptyEnv) emptyPrfEnv 
--   case c of
--     Left e -> print $ disp e
--     Right a -> print $ disp ((fst . fst) a)

--tr1 = In (MVar "n" Ind) (In (MVar "U" (To Ind Form)) (MVar "Vec" (To (To Ind Form) (To Ind (To Ind Form)))))
-- compTest1 :: IO ()
-- compTest1 = do
--   b <- runErrorT $ runStateT (runReaderT (runGlobal (compEType tr1 )) emptyEnv) emptyPrfEnv
--   case b of
--     Left e -> putStrLn e
--     Right a ->
--       putStrLn $ show $ fst a

