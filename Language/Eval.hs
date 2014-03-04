module Language.Eval (reduce, parSimp) where
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

step (Lambda x t) s = return $ Lambda x t
-- to use head reduction, replace the line above by the following line 
-- step t s >>= \a -> return $ Lambda x a

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
  -- for term what we really need is just syntactic
  -- comparison here
  if m == n then return m else reduce m

-- simplifying proof
simp :: PreTerm -> S.Set VName -> Global PreTerm

simp (App (Lambda x p1) p2 ) s = return $ runSubst p2 (PVar x) p1

simp (PApp (PLam x p1) p2 ) s = return $ runSubst p2 (PVar x) p1

simp (PFApp (PLam x p1) t ) s = return $ runSubst t (PVar x) p1

simp (PFApp (PVar x) t) s =
  if x `S.member` s then do
    e <- get
    case M.lookup x (tacticDef e) of
      Just a -> return $ PFApp a t
      Nothing -> return $ PFApp (PVar x) t
  else return $ PFApp (PVar x) t

simp (App (PVar x) t) s =
  if x `S.member` s then do
    e <- get
    case M.lookup x (progDef e) of
      Just a -> return $ App a t
      Nothing -> return $ App (PVar x) t
  else return $ App (PVar x) t

simp (PApp t1 t2) s = do
  a1 <- simp t1 s
  a2 <- simp t2 s
  return $ PApp a1 a2

simp (App t1 t2) s = do
  a1 <- simp t1 s
  a2 <- simp t2 s
  return $ App a1 a2

simp (PFApp p1 t) s = 
  simp p1 s >>= \ a -> return $ PFApp a t

simp (PLam x t) s =
  simp t s >>= \a -> return $ PLam x a

simp (Lambda x t) s =
  simp t s >>= \a -> return $ Lambda x a

simp (PVar x) s = 
  if x `S.member` s then do
    e <- get
    case M.lookup x (tacticDef e) of
      Just t -> return t
      Nothing -> case M.lookup x (progDef e) of
                    Just t1 -> return t1
                    Nothing -> return $ PVar x
  else return $ PVar x

simp (MP p1 p2) s = do
  a1 <- simp p1 s
  a2 <- simp p2 s
  return $ MP a1 a2

simp (Inst p1 t) s = 
  simp p1 s >>= \ a1 -> return $ Inst a1 t

simp (InvCmp p1 t) s = 
  simp p1 s >>= \ a1 -> return $ InvCmp a1 t

simp (InvBeta p1 t) s = 
  simp p1 s >>= \ a1 -> return $ InvBeta a1 t

simp (Cmp p1) s = 
  simp p1 s >>= \ a1 -> return $ Cmp a1 

simp (Beta p1) s = 
  simp p1 s >>= \ a1 -> return $ Beta a1 

simp (UG x p1) s = 
  simp p1 s >>= \ a1 -> return $ UG x a1 

simp (Discharge x t p1) s = 
  simp p1 s >>= \ a1 -> return $ Discharge x t a1 

simp (Pos pos p1) s = simp p1 s -- `catchError` addProofErrorPos pos p1

simp _ _ = die "Wrong use of proof simplication."

-- for parSimp, its goal is to reduce/simplify
-- tactic to its normal-form, so that proof-checking
-- can proceed without problem. And it is not for compiling
-- to run, so it is fine to be inefficient.
parSimp :: PreTerm -> Global PreTerm
parSimp t = do
  m <- simp t (fv t)
  n <- simp m (fv m)
  if m == n then return m else parSimp m


          
