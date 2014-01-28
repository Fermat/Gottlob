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
import Control.Monad.State
import Control.Monad.Error
import qualified Data.Map as M
import Control.Applicative hiding (empty)
import Control.Monad.Reader
import Control.Monad.Error

newtype Global a =
  Global {runGlobal :: StateT Env (StateT PrfEnv (ErrorT String IO)) a }
  deriving (Functor, Applicative, Monad,
             MonadState Env, MonadError String, MonadIO)

data Env = Env{
               progDef::M.Map VName PreTerm,
               setDef::M.Map VName PreTerm,
               gamma::M.Map VName EType,
               proofCxt::M.Map VName (ProofScripts, PreTerm)
              }

data PrfEnv = PrfEnv {
               assumption::[(VName, PreTerm)],
               localProof :: M.Map VName (Proof, PreTerm)
               }

emptyEnv :: Env
emptyEnv = Env {progDef = M.empty, setDef = M.empty, gamma = M.empty,
                proofCxt=M.empty}

emptyPrfEnv :: PrfEnv
emptyPrfEnv = PrfEnv { assumption = [],
                localProof=M.empty}

extendProgDef :: VName -> PreTerm -> Env -> Env
extendProgDef v t e@(Env {progDef}) = e{progDef = M.insert v t progDef}

extendGamma :: VName -> EType -> Env -> Env
extendGamma v t e@(Env {gamma}) = e{gamma = M.insert v t gamma}

extendSetDef :: VName -> PreTerm -> Env -> Env
extendSetDef v t e@(Env {setDef}) = e{setDef = M.insert v t setDef}

pushAssump :: VName -> PreTerm -> PrfEnv -> PrfEnv
pushAssump v f e@(PrfEnv {assumption}) = e{assumption = (v,f):assumption}

popAssump :: PrfEnv -> PrfEnv
popAssump e@(PrfEnv {assumption}) = e{assumption = tail assumption}

extendLocalProof :: VName -> Proof -> PreTerm -> PrfEnv -> PrfEnv
extendLocalProof v p f e@(PrfEnv {localProof}) = e{localProof = M.insert v (p,f) localProof}
