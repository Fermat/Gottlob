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
import Data.List
import Control.Monad.Error
import qualified Data.Map as M
import qualified Data.Set as S
-- process parsing data 
checkDefs :: Module -> IO (Either PCError (Env, PrfEnv))
checkDefs (Module mod l) = do
 a <- runErrorT $ runStateT (runStateT (process l) emptyEnv) emptyPrfEnv
 case a of
   Left e -> return $ Left e
   Right b -> return $ Right ((snd.fst) b, snd b)
   
process :: [Decl] -> Global ()
process [] = return ()
-- process ((DeclPos pos d):l) =
--   process (d:l) `catchError` addDeclErrorPos pos d
process((FormOperatorDecl _ _ _):l) = process l
process((SpecialOperatorDecl _ _ _):l) = process l
process((ProgOperatorDecl _ _ _):l) = process l
process ((ProgDecl x p):l) = do
  emit $ "processing prog decl" <++> x
  st <- get
  put $ extendProgDef x (progTerm p) st
  process l

process ((DataDecl pos d):l) =
  let progs = toScott d d   
      sd = toSet d
  in
  do
    emit $ "processing data decl" <++> (fst sd)
    (wellDefined $ snd sd) `catchError` addPreErrorPos pos (snd sd)
    (t, res, _) <- (withErrorInfo "During the set transformation" [(disp "The target set", disp (snd sd))] (wellFormed $ snd sd))
                   `catchError` addPreErrorPos pos (snd sd)
    state <- get
    let s1 = extendSetDef (fst sd) (snd sd) t state
        s3 = foldl' (\ z x -> extendProgDef (fst x) (snd x) z) s1 progs in
      put s3
    process l

process ((SetDecl x set):l) = do
  let pos = getFirstPos set
  emit $ "processing set decl" <++> x
  when (isTerm $ set) $ (pcError
    "Improper set definition. Can't define a set as a term" [(disp "Definiendum",disp x),(disp "Defininen", disp set)])
    `catchError` addPreErrorPos pos set
  (wellDefined set) `catchError` addPreErrorPos pos set
  (t, res, _) <- (wellFormed set) `catchError` addPreErrorPos pos set
  state <- get
  put $ extendSetDef x set t state
  process l

process ((ProofDecl n ps f):l) = do
  emit $ "processing proof decl" <++> n
  wellDefined f 
  (t, c, d) <- ensureForm f
  lift $ put $ newPrfEnv d -- default type def for the proofs.
  proofCheck ps
  let (_,_, (Pos pos f0))= last ps
  (sameFormula f0 f) `catchError` addPreErrorPos pos f0
  updateProofCxt n ps f
  emptyLocalProof
  process l

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
