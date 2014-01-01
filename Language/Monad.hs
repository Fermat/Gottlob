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
  Global {runGlobal :: ReaderT Env (StateT PrfEnv (ErrorT String IO)) a }
  deriving (Functor, Applicative, Monad,
            MonadReader Env, MonadState PrfEnv, MonadError String, MonadIO)

data Env = Env{
               def::M.Map VName (EType, Meta),
               gamma::M.Map VName EType,
               proofCxt::M.Map VName (ProofScripts, Meta)
              }

data PrfEnv = PrfEnv {
               assumption::[(VName, Meta)],
               localProof :: M.Map VName (Proof, Meta)
               }

emptyEnv :: Env
emptyEnv = Env {def = M.empty, gamma = M.empty,
                proofCxt=M.empty}

emptyPrfEnv :: PrfEnv
emptyPrfEnv = PrfEnv { assumption = [],
                localProof=M.empty}

extendGamma :: VName -> EType -> Env -> Env
extendGamma v t e@(Env {gamma}) = e{gamma = M.insert v t gamma}

pushAssump :: VName -> Meta -> PrfEnv -> PrfEnv
pushAssump v f e@(PrfEnv {assumption}) = e{assumption = (v,f):assumption}

popAssump :: PrfEnv -> PrfEnv
popAssump e@(PrfEnv {assumption}) = e{assumption = tail assumption}
