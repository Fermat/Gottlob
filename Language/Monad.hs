{-# LANGUAGE DeriveDataTypeable         #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE NamedFieldPuns             #-}
{-# LANGUAGE PackageImports             #-}
{-# LANGUAGE ParallelListComp           #-}
{-# LANGUAGE TypeSynonymInstances       #-}
{-# LANGUAGE DeriveFunctor #-}
module Language.Monad where
import Language.Syntax
import Language.PrettyPrint
import Text.PrettyPrint
import Control.Monad.State
import Control.Monad.Error
import qualified Data.Map as M
import Control.Applicative hiding (empty)
import Control.Monad.Reader
import Control.Monad.Error
-- PrfEnv should be a reader?
type Global a = StateT Env (StateT PrfEnv (ErrorT String IO)) a
  -- Global {runGlobal ::  }
  -- deriving (Functor, Applicative, Monad,
  --            MonadState Env, MonadError String, MonadIO)

data Env = Env{
               progDef::M.Map VName PreTerm,
               setDef::M.Map VName (PreTerm, EType),
               proofCxt::M.Map VName (ProofScripts, PreTerm)
              }
         deriving Show

data PrfEnv = PrfEnv {
               assumption::[(VName, PreTerm)],
               localProof :: M.Map VName (Proof, PreTerm),
               localEType :: M.Map VName EType
               }
            deriving Show

emit :: (Show a, MonadIO m) => a -> m ()
emit m = liftIO $ print m

emptyEnv :: Env
emptyEnv = Env {progDef = M.empty, setDef = M.empty,
                proofCxt=M.empty}

emptyPrfEnv :: PrfEnv
emptyPrfEnv = PrfEnv { assumption = [],
                localProof=M.empty, localEType=M.empty}

newPrfEnv :: [(VName, EType)] -> PrfEnv
newPrfEnv e = PrfEnv { assumption = [],
                localProof=M.empty, localEType=M.fromList e}
                  
extendProgDef :: VName -> PreTerm -> Env -> Env
extendProgDef v t e@(Env {progDef}) = e{progDef = M.insert v t progDef}

extendProofCxt :: VName -> ProofScripts -> PreTerm -> Env -> Env
extendProofCxt v ps f e@(Env {proofCxt}) = e{proofCxt = M.insert v (ps,f) proofCxt}

extendSetDef :: VName -> PreTerm -> EType -> Env -> Env
extendSetDef v t t1 e@(Env {setDef}) = e{setDef = M.insert v (t, t1) setDef}

pushAssump :: VName -> PreTerm -> PrfEnv -> PrfEnv
pushAssump v f e@(PrfEnv {assumption}) = e{assumption = (v,f):assumption}

popAssump :: PrfEnv -> PrfEnv
popAssump e@(PrfEnv {assumption}) = e{assumption = tail assumption}

extendLocalProof :: VName -> Proof -> PreTerm -> PrfEnv -> PrfEnv
extendLocalProof v p f e@(PrfEnv {localProof}) = e{localProof = M.insert v (p,f) localProof}

extendLocalEType :: VName -> EType -> PrfEnv -> PrfEnv
extendLocalEType v p e@(PrfEnv {localEType}) = e{localEType = M.insert v p localEType}
--------------

instance Disp Env where
  disp env = hang (text "Program Definitions") 2 (vcat
                [disp n <+> text "=" <+> disp t | (n, t) <- M.toList $ progDef env])  $$
             hang (text "Set/Formula Definitions") 2 (vcat
                                                      [disp n <+> text":"<+> disp t <+> text "=" <+> disp f | (n,(f,t)) <- M.toList $ setDef env]) $$
             hang (text "Proofs Context") 2 (vcat
                [ disp (ProofDecl n ps f) | (n,(ps,f)) <- M.toList $ proofCxt env])

instance Disp PrfEnv where
  disp env = hang (text "Current Local Assumptions") 2 (vcat
                [parens (disp n) <+> text ":" <+> disp t | (n, t) <- assumption env])  $$
             hang (text "Local Proofs") 2 (vcat
                                           [disp n <+> text"="<+> disp p <+> text ":" <+> disp f | (n,(p,f)) <- M.toList $ localProof env]) $$
             hang (text "Local EType Assigments") 2 (vcat
                [ disp n <+> text ":" <+> disp t | (n,t) <- M.toList $ localEType env])
