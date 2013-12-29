{-# LANGUAGE NamedFieldPuns #-}

module Language.Monad where
import Language.Syntax
import Control.Monad.State.Lazy
import qualified Data.Map as M

type PCMonad a = State Env (Either String a)
data Env = Env{
               def::M.Map VName Meta,
               gamma::M.Map VName EType,
               assumption::[(VName, Meta)],
               localProof :: M.Map VName (Proof, Meta),
               proofCxt::M.Map VName (ProofScripts, Meta)
              }

emptyEnv :: Env
emptyEnv = Env {def = M.empty, gamma = M.empty,
                assumption=[], localProof = M.empty, proofCxt=M.empty}
