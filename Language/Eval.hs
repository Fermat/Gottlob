module Language.Eval (reduce, simp) where
import Language.Syntax
import Language.Monad
import Language.PrettyPrint

import Control.Monad.State.Lazy
import Control.Monad.Reader
import Control.Monad.Error

import qualified Data.Map as M
import qualified Data.Set as S

reduce :: PreTerm -> Global PreTerm
reduce (App (Lambda x t1) t2 ) = reduce $ runSubst t2 (PVar x) t1

reduce (App t1 t2) = do
  a <- reduce t1
  if isLambda a
    then reduce $ App a t2
    else return $ App a t2
  where isLambda (Lambda x t) = True
        isLambda _ = False

reduce (Lambda x t) = return $ Lambda x t

reduce (PVar x) = 
  do
    e <- get
    case M.lookup x (progDef e) of
      Nothing -> return $ PVar x
      Just t -> reduce t


reduce t = die $ "unhandle reduction for term" <++> disp t

simp ::  PreTerm -> Global PreTerm
simp (App (Lambda x p1) p2 ) = simp $ runSubst p2 (PVar x) p1 

simp (App (PVar x) t) = do
    emit $ "continuing reduction with " <++> disp x  
    e <- get
    case M.lookup x (progDef e) of
      Just a -> do
        simp $ App a t
      Nothing ->
        case M.lookup x (tacticDef e) of
          Just a -> do
            simp $ App a t
          Nothing -> do
            t1 <- simp t
            return $ App (PVar x) t1

simp (App t1 t2) = do
  a1 <- simp t1 
  a2 <- simp t2 
  if isLambda a1
    then simp $ App a1 t2
    else return $ App a1 t2
  where isLambda (Lambda x t) = True
        isLambda _ = False

simp (Lambda x t) = return $ Lambda x t

simp (PVar x) = do
    e <- get
    case M.lookup x (tacticDef e) of
      Just t -> simp t
      Nothing -> case M.lookup x (progDef e) of
                    Just t1 -> simp t1
                    Nothing -> return $ PVar x

simp (MP p1 p2) = do
  a1 <- simp p1
  a2 <- simp p2
  return $ MP a1 a2

simp (Inst p1 t) = 
  simp p1 >>= \ a1 -> return $ Inst a1 t

simp (InvCmp p1 t) = 
  simp p1 >>= \ a1 -> return $ InvCmp a1 t

simp (InvSimp p1 t) = 
  simp p1 >>= \ a1 -> return $ InvSimp a1 t

simp (InvBeta p1 t) = 
  simp p1 >>= \ a1 -> return $ InvBeta a1 t

simp (Cmp p1) = 
  simp p1 >>= \ a1 -> return $ Cmp a1 

simp (SimpCmp p1) = 
  simp p1 >>= \ a1 -> return $ SimpCmp a1 

simp (Beta p1) = 
  simp p1 >>= \ a1 -> return $ Beta a1 

simp (UG x p1) = 
  simp p1 >>= \ a1 -> return $ UG x a1 

simp (Discharge x t p1) = 
  simp p1 >>= \ a1 -> return $ Discharge x t a1 

simp (a@(Forall _ _)) = return a
simp (a@(Imply _ _)) = return a
simp (a@(Iota _ _)) = return a
simp (a@(In _ _)) = return a
simp (a@(SApp _ _)) = return a
simp (a@(TApp _ _)) = return a

simp (Pos pos p1) = simp p1 -- `catchError` addProofErrorPos pos p1

simp p = die $ "Wrong use of proof simplication." <++> disp p

