module Language.Preprocess where
import Language.TypeInference
import Language.ProofChecking
import Language.PrettyPrint
import Language.Syntax
import Language.Program
import Language.Monad

import Text.Parsec.Pos

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
 a <- runErrorT $ runReaderT (runStateT (runStateT (process l) emptyEnv) emptyPrfEnv) []
 case a of
   Left e -> return $ Left e
   Right b -> return $ Right ((snd.fst) b, snd b)
   
process :: [Decl] -> Global ()
process [] = return ()
process((FormOperatorDecl _ _ _):l) = process l
process((ProgOperatorDecl _ _ _):l) = process l
process ((ProgDecl x p):l) = do
  emit $ "processing prog decl" <++> x
  st <- get
  case M.lookup x $ progDef st of
    Nothing -> do
      put $ extendProgDef x (progTerm p) st
      process l
    Just a ->
     die "The program has been defined."
     `catchError` addProgErrorPos (getProgPos p) (Name x)

process ((DataDecl pos d):l) =
  let progs = toScott d    
      sd = toSet d
      sdd = snd sd in do
    emit $ "processing data decl" <++> (fst sd)
    wellDefined sdd `catchError` addPreErrorPos pos sdd
    (t, res, _) <- withErrorInfo "During the set transformation"
                   [(disp "The target set", disp (snd sd))] (wellFormed sdd)
                   `catchError` addPreErrorPos pos sdd
    state <- get
    let s1 = extendSetDef (fst sd) sdd t state
        s3 = foldl' (\ z (x1, x2) -> extendProgDef x1 x2 z) s1 progs in
      put s3
    process l

process ((SetDecl x set):l) = do
  let pos = getFirstPos set
  emit $ "processing set decl" <++> x
  a <- isTerm set
  when a $ pcError "Improper set definition. Can't define a set as a term"
    [(disp "Definiendum",disp x),(disp "Defininen", disp set)]
    `catchError` addPreErrorPos pos set
  wellDefined set `catchError` addPreErrorPos pos set
  (t, res, _) <- wellFormed set `catchError` addPreErrorPos pos set
  state <- get
  put $ extendSetDef x set t state
  process l

process ((ProofDecl n ps f):l) = do
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
      process l
    Nothing -> die "Impossible situation."

process ((TacDecl x args (Left p)):l) = do 
  emit $ "processing tactic decl" <++> x
  st <- get
  case M.lookup x $ tacticDef st of
    Nothing -> do
      let a = foldr (\ x z -> PLam x z) p args
      put $ extendTacticDef x a st
      process l
    Just a ->
     die "The tactic has been defined."
     `catchError` addProofErrorPos (getProofPos p) (PrVar x)

process ((TacDecl x args (Right ps)):l) = do 
  emit $ "processing tactic decl" <++> x
  st <- get
  case M.lookup x $ tacticDef st of
    Nothing -> do
      let p = runToProof ps
          a = foldr (\ x z -> PLam x z) p args
      put $ extendTacticDef x a st
      process l
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

getProofPos :: Proof -> SourcePos
getProofPos (PPos pos p) =  pos
getProofPos (_) = error "Fail to get First Position"
