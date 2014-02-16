module Language.Eval (reduce) where
import Language.Syntax
import Language.Monad
import Language.PrettyPrint

import Control.Monad.State.Lazy
import Control.Monad.Reader
import Control.Monad.Error

import qualified Data.Map as M
import qualified Data.Set as S

step :: PreTerm -> S.Set VName -> Global PreTerm
step (App (Lambda x t1) t2 ) s = return $ runSubst t2 (PVar x) t1

step (App t1 t2) s = step t1 s >>= \ a -> return $ App a t2

step (Lambda x t) s = step t s >>= \a -> return $ Lambda x a

step (PVar x) s = 
  if x `S.member` s then do
    e <- get
    case M.lookup x (progDef e) of
      Nothing -> do
      --  emit $ "continuing reduction with free prog variable" <++> x
        return $ PVar x
      Just t -> return t
  else return $ PVar x
step _ _ = die "Wrong use of eval/reduction."

reduce :: PreTerm -> Global PreTerm
reduce t = do
  m <- step t (fv t)
  n <- step m (fv m)
  if m == n then return m else reduce m


simp :: Proof -> Global Proof
simp (PApp (PLam x p1) p2 ) = return $ subProof p2 (PrVar x) p1
simp (PFApp (PLam x p1) t ) = return $ subPre t (PVar x) p1
simp (PFApp (PrVar x) t ) = do
  e <- get
  case M.lookup x (tacticDef e) of
    Nothing -> do
      --  emit $ "continuing reduction with free prog variable" <++> x
      return $ PVar x
    Just t -> return t

step (App t1 t2) s = step t1 s >>= \ a -> return $ App a t2

step (Lambda x t) s = step t s >>= \a -> return $ Lambda x a

step (PVar x) s = 
  if x `S.member` s then do
    e <- get
    case M.lookup x (progDef e) of
      Nothing -> do
      --  emit $ "continuing reduction with free prog variable" <++> x
        return $ PVar x
      Just t -> return t
  else return $ PVar x
step _ _ = die "Wrong use of eval/reduction."


          
