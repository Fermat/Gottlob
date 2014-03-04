module Language.Eval (reduce, simp) where
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
  if m == n then return m else reduce m

-- simplifying proof
simp :: S.Set VName -> PreTerm -> Global PreTerm
simp s (App (Lambda x p1) p2 ) = do
--  emit $ "continuing reduction with " <++> x
  simp s $ runSubst p2 (PVar x) p1 

simp s (App (PVar x) t) = do
  emit $ "continuing reduction here:" <++> disp x
  emit $ "a list of fv " ++ show s
  if x `S.member` s
    then do
    e <- get
    case M.lookup x (progDef e) of
      Just a -> do
        emit $ "reducing1 " <++> (disp $ App a t)
        simp s $ App a t
      Nothing ->
        case M.lookup x (tacticDef e) of
          Just a -> do
            emit $ "reducing " <++> (disp $ App a t)
            simp s $ App a t
          Nothing -> do
            emit $ "reducing2 " <++> (disp $ t)
            t1 <- simp s t
            return $ App (PVar x) t1
    else do
    emit $ "reducing3 "
    return $ App (PVar x) t

-- simp (PApp t1 t2) s = do
--   a1 <- simp t1 s
--   a2 <- simp t2 s
--   return $ PApp a1 a2

simp s (App t1 t2) = do
  a1 <- simp s t1 
--  a2 <- simp t2 s
  simp s $ App a1 t2

-- simp (PFApp p1 t) s = 
--   simp p1 s >>= \ a -> return $ PFApp a t

-- simp (PLam x t) s =
--   simp t s >>= \a -> return $ PLam x a

simp s (Lambda x t) = return $ Lambda x t

simp s (PVar x) = do
  emit $ "continuing reduction with " <++> disp x  
  if x `S.member` s
    then do
    e <- get
    case M.lookup x (tacticDef e) of
      Just t -> simp s t
      Nothing -> case M.lookup x (progDef e) of
                    Just t1 -> simp s t1
                    Nothing -> return $ PVar x
    else return $ PVar x

simp s (MP p1 p2) = do
  a1 <- simp s p1
  a2 <- simp s p2
  return $ MP a1 a2

simp s (Inst p1 t) = 
  simp s p1 >>= \ a1 -> return $ Inst a1 t

simp s (InvCmp p1 t) = 
  simp s p1 >>= \ a1 -> return $ InvCmp a1 t

simp s (InvBeta p1 t) = 
  simp s p1 >>= \ a1 -> return $ InvBeta a1 t

simp s (Cmp p1) = 
  simp s p1 >>= \ a1 -> return $ Cmp a1 

simp s (Beta p1) = 
  simp s p1 >>= \ a1 -> return $ Beta a1 

simp s (UG x p1) = 
  simp s p1 >>= \ a1 -> return $ UG x a1 

simp s (Discharge x t p1) = 
  simp s p1 >>= \ a1 -> return $ Discharge x t a1 

simp s (a@(Forall _ _)) = return a
simp s (a@(Imply _ _)) = return a
simp s (a@(Iota _ _)) = return a
simp s (a@(In _ _)) = return a
simp s (a@(SApp _ _)) = return a
simp s (a@(TApp _ _)) = return a

simp s (Pos pos p1) = simp s p1 -- `catchError` addProofErrorPos pos p1

simp s p = die $ "Wrong use of proof simplication." <++> disp p

-- for parSimp, its goal is to reduce/simplify
-- tactic to its normal-form, so that proof-checking
-- can proceed without problem. And it is not for compiling
-- to run, so it is fine to be inefficient.
-- parSimp :: PreTerm -> Global PreTerm
-- parSimp t = do
--   m <- simp t (fv t)
--   n <- simp m (fv m)
--   if m == n then return m else parSimp m


          
