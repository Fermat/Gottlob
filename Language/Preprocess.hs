module Language.Preprocess where
import Language.TypeInference
import Language.ProofChecking
import Language.Syntax
import Language.Program
import Language.Monad
import Control.Monad.Identity
import Control.Monad.State
import Data.List
import Control.Monad.Error
import qualified Data.Map as M
import qualified Data.Set as S
-- process parsing data 
checkDefs :: Module -> IO (Either String (Env, PrfEnv))
checkDefs (Module mod l) = do
 a <- runErrorT $ runStateT (runStateT (process l) emptyEnv) emptyPrfEnv
 case a of
   Left e -> return $ Left e
   Right b -> return $ Right ((snd.fst) b, snd b)
   
process :: [Decl] -> Global ()
process [] = return ()
process((FormOperatorDecl _ _ _):l) = process l
process((SpecialOperatorDecl _ _ _):l) = process l
process((ProgOperatorDecl _ _ _):l) = process l
process ((ProgDecl x p):l) = do
  emit $ "processing prog decl" <++> x
  st <- get
  put $ extendProgDef x (progTerm p) st
  process l

process ((DataDecl d):l) =
  let progs = toScott d d   
      sd = toSet d in
  do
    emit $ "processing data decl" <++> (fst sd)
    wellDefined $ snd sd
    (t, res, _) <- wellFormed $ snd sd
    state <- get
    let s1 = extendSetDef (fst sd) (snd sd) t state
        s3 = foldl' (\ z x -> extendProgDef (fst x) (snd x) z) s1 progs in
      put s3
    process l

process ((SetDecl x set):l) = do
  emit $ "processing set decl" <++> x
  when (isTerm $ set) $ pcError "Improper set definition." [(disp "Definiendum",disp x),
                                                            (disp "Definien", disp set)]   
  wellDefined set 
  (t, res, _) <- wellFormed set
  state <- get
  put $ extendSetDef x set t state
  process l

process ((ProofDecl n ps f):l) = do
  emit $ "processing proof decl" <++> n
  wellDefined f 
  (t, c, d) <- ensureForm f
  lift $ put $ newPrfEnv d -- default type def for the proofs.
  proofCheck ps
  let (_,_, f0)= last ps
  ensureEq f0 f
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

