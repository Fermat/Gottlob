module Language.Preprocess where
import Language.TypeInference
import Language.Induction
import Language.ProofChecking
import Language.PrettyPrint
import Language.Syntax
import Language.Program
import Language.Monad
import Language.Pattern

import Text.Parsec.Pos
import Text.PrettyPrint

import Control.Monad.Identity
import Control.Monad.State
import Control.Monad.Error
import Control.Monad.Reader

import Data.List
import qualified Data.Map as M
import qualified Data.Set as S

-- process parsed data 
checkDefs :: Module -> IO (Either PCError (Env, PrfEnv))
checkDefs (Module mod l) = do
 a <- runErrorT $ runReaderT (runStateT (runStateT (process l l) emptyEnv) emptyPrfEnv) []
 case a of
   Left e -> return $ Left e
   Right b -> return $ Right ((snd.fst) b, snd b)
   
process :: [Decl] -> [Decl] -> Global ()
process state [] = return ()
process state ((FormOperatorDecl _ _ _):l) = process state l
process state ((ProofOperatorDecl _ _ _):l) = process state l
process state ((ProgOperatorDecl _ _ _):l) = process state l

process state ((ProgDecl x p):l) = do
  emit $ "processing prog decl" <++> x
  st <- get
  case M.lookup x $ progDef st of
    Nothing -> do
      put $ extendProgDef x (progTerm p) st
      process state l
    Just a ->
     die "The program has been defined."
     `catchError` addProgErrorPos (getProgPos p) (Name x)

process state ((PatternDecl x pats p):l) = 
  let (a, ls) = getAll [(PatternDecl x pats p)] x l
      lth = length pats in do
    emit $ "processing prog decl" <++> x
--    emit $ hsep (map disp  )
    checkArity a lth
    eqs <- mapM (toEquation state) a
    let 
        args = [makeVar i | i <- [1..lth] ]
        prog = Abs args (match state lth args eqs (Name "Error"))
    st <- get
    emit $ disp prog
    case M.lookup x $ progDef st of
      Nothing -> do
        put $ extendProgDef x (progTerm prog) st
        process state ls
      Just a ->
        die "The program has been defined."
      `catchError` addProgErrorPos (getProgPos p) (Name x)
      where makeVar i = "_u"++ show i
            getAll s x r@((PatternDecl y pats' p'):ys)
              | x == y = 
                getAll ((PatternDecl y pats' p'):s) x ys
              | otherwise = (s, r)
            getAll s x r = (s, r)
            checkArity [] lth = return ()
            checkArity ((PatternDecl y pats' p'):ys) lth =
              if length pats' == lth then checkArity ys lth
              else die $ "Different arity for the same function." <++> disp lth <++> disp y 

process state ((DataDecl pos d False):l) =
  let progs = toScott d    
      sd = toSet d
      sdd = snd sd in do
    emit $ "processing data decl" <++> (fst sd)
    sdd1 <- repeatComp False sdd
    wellDefined sdd1 `catchError` addPreErrorPos pos sdd1
    (t, res, _) <- withErrorInfo "During the set transformation"
                   [(disp "The target set", disp (snd sd))] (wellFormed sdd)
                   `catchError` addPreErrorPos pos sdd
    state1 <- get
    let s1 = extendSetDef (fst sd) sdd1 t state1
        s3 = foldl' (\ z (x1, x2) -> extendProgDef x1 x2 z) s1 progs in
      put s3
    emptyLocalProof
    process state l

process state ((DataDecl pos d True):l) =
  let progs = toScott d    
      sd = toSet d
      sdd = snd sd in
   do
    emit $ "processing data decl" <++> (fst sd)
    sdd1 <- repeatComp False sdd
    let indF = getInd sdd1
        indP = runDerive indF
    wellDefined sdd1 `catchError` addPreErrorPos pos sdd1
    (t, res, _) <- withErrorInfo "During the set transformation"
                   [(disp "The target set", disp sdd1)] (wellFormed sdd1)
                   `catchError` addPreErrorPos pos sdd1
    state1 <- get
    let s1 = extendSetDef (fst sd) sdd1 t state1
        s3 = foldl' (\ z (x1, x2) -> extendProgDef x1 x2 z) s1 progs in
      put s3
    ih <- checkFormula indP `catchError` addPreErrorPos pos indP
    withErrorInfo "During the automatic derivation"
                   [(disp "The target formula ", disp ih)] (wellFormed ih)
                   `catchError` addPreErrorPos pos ih
    sameFormula ih indF `catchError` addPreErrorPos pos ih
    state1 <- get
    let s2 = extendSetDef ("Ind"++fst sd) ih Form state1
        s4 = extendProofCxt ("ind"++fst sd) [("p", Right indP, Nothing)] ih s2 in
      put s4
    emptyLocalProof
    process state l

process state ((SetDecl x set):l) = do
  let pos = getFirstPos set
  emit $ "processing set decl" <++> x
  a <- isTerm set
  when a $ pcError "Improper set definition. Can't define a set as a term"
    [(disp "Definiendum",disp x),(disp "Defininen", disp set)]
    `catchError` addPreErrorPos pos set
  wellDefined set `catchError` addPreErrorPos pos set
  (t, res, _) <- wellFormed set `catchError` addPreErrorPos pos set
  state1 <- get
  put $ extendSetDef x set t state1
  emptyLocalProof
  process state l

process state ((ProofDecl n (Just m) ps f):l) = do
  emit $ "processing proof decl" <++> n <++> disp m
  wellDefined f 
  (t, c, d) <- ensureForm f
  env <- get
  put $ extendSetDef m (erased f) Form env 
  lift $ put $ newPrfEnv d -- default type def for the proofs.
  proofCheck ps
  let (x,_, _)= last ps
  localEnv <- lift $ get
  case M.lookup x (localProof localEnv) of
    Just (_ , PVar f0) | f0 == m -> do
      updateProofCxt n ps f
      emptyLocalProof
      process state l
    Just (_, f0) -> do
--      emit $ show f0 
      sameFormula f0 f
      updateProofCxt n ps f
      emptyLocalProof
      process state l
    Nothing -> die "Impossible situation. Ask Frank to keep hacking."

process state ((ProofDecl n Nothing ps f):l) = do
  emit $ "processing proof decl" <++> n
  wellDefined f 
  (t, c, d) <- ensureForm f
  lift $ put $ newPrfEnv d -- default type def for the proofs.
  proofCheck ps
  let (x,_, _)= last ps
  localEnv <- lift $ get
  case M.lookup x (localProof localEnv) of
    Just (_ , f0) -> do
      sameFormula f0 f 
      updateProofCxt n ps f
      emptyLocalProof
      process state l
    Nothing -> die "Impossible situation."

process state ((TacDecl x args (Left p)):l) = do 
  emit $ "processing tactic decl" <++> x
  st <- get
  case M.lookup x $ tacticDef st of
    Nothing -> do
      let a = foldr (\ x z -> Lambda x z) (progTerm p) args
      put $ extendTacticDef x a st
      process state l
    Just a ->
     die "The tactic has been defined."
--     `catchError` addProofErrorPos (getProofPos p) (PVar x)

process state ((TacDecl x args (Right ps)):l) = do 
  emit $ "processing tactic decl" <++> x
  st <- get
  case M.lookup x $ tacticDef st of
    Nothing -> do
      let p = runToProof ps
          a = foldr (\ x z -> Lambda x z) p args
      put $ extendTacticDef x a st
      process state l
    Just a ->
      die $ "The tactic has been defined. Namely, " <++> disp x


isTerm :: PreTerm -> Global Bool
isTerm p = do
  (a, _, _) <- wellFormed p
  return $ a == Ind

emptyLocalProof :: Global()
emptyLocalProof = do
  lift $ put emptyPrfEnv
  return ()
  
updateProofCxt :: VName -> ProofScripts -> PreTerm -> Global()
updateProofCxt n ps f = do
  env <- get
  put $ extendProofCxt n ps f env
  return ()

getFirstPos :: PreTerm -> SourcePos
getFirstPos (Pos pos p) =  pos
getFirstPos (Iota x p) =  getFirstPos p
getFirstPos (_) = error "Fail to get First Position"

getProgPos :: Prog -> SourcePos
getProgPos (ProgPos pos p) =  pos
getProgPos (Abs xs p) =  getProgPos p
getProgPos (_) = error "Fail to get First Position"

toEquation :: [Decl] -> Decl -> Global Equation
toEquation state (PatternDecl y pats p) = do
  patterns <- mapM (\x -> toPat x state) pats
  return $ (patterns, p)
    where toPat (Name c) state = 
            if isConstr c state then
              return $ (Cons c [])
            else return $ (Var c)
          toPat (Applica (Name c) b) state =
            if isConstr c state then
              return $ Cons c (toVar b)
            else die $ "non constructor: " <++> disp c
          toPat (Applica a b) state = do
            (Cons v ls) <- toPat a state
            return $ Cons v (ls ++ (toVar b))
          toPat (ProgPos pos p) state = toPat p state
          toVar (Name a) = [Var a]
          toVar (Applica a b) = (toVar a) ++ (toVar b)

isConstr v ((DataDecl pos (Data name params cons) b):l) =
  case lookup v cons of
    Just _ -> True
    Nothing -> isConstr v l

isConstr v (x:l) = isConstr v l
isConstr v [] = False

  
-- getProofPos :: Pre -> SourcePos
-- getProofPos (PPos pos p) =  pos
-- getProofPos (_) = error "Fail to get First Position"

