module Language.Induction where
import Language.Syntax
import Language.PrettyPrint
import Control.Monad.Reader
import Control.Monad.Identity
import Control.Monad.State.Lazy


import Data.List
import Data.Char

-- take in a inductive set def and return
-- a proof of its induction principle
-- rename :: PreTerm -> PreTerm -> PreTerm
-- derive :: PreTerm -> (VName, PreTerm, PreTerm)

-- set to ind principle
-- set -> formula
toFormula :: PreTerm -> PreTerm
toFormula (Iota x (Iota y p)) = Forall x (toFormula p)
toFormula (Iota x (Forall y p)) = Forall y $ tailAppend x p
  where tailAppend x (Imply f1 (Imply f2 f3)) = Imply f1 (Imply f2 (tailAppend x f3))
        tailAppend x (Imply f1 f2) = Imply f1 $ Forall x (Imply (change f2) f2)
        change (In x (PVar y)) = In x (PVar (y++"1"))
        change (In x (SApp (PVar y) s)) = In x (SApp (PVar (y++"1")) s)
        change (In x (TApp (PVar y) s)) = In x (TApp (PVar (y++"1")) s)

-- ind -> proof
type Env a = ReaderT [VName] (StateT Int Identity) a
runDerive :: PreTerm -> PreTerm
runDerive t = fst $ runIdentity $ runStateT (runReaderT (deriveInd t) []) 0

deriveInd :: PreTerm -> Env PreTerm
deriveInd (Forall x f) = do
  f1 <- deriveInd f
  return $ UG x f1
  
deriveInd (Imply f1 f2) = do
  n <- get
  modify (+1)
  f3 <- local (\l -> ("a"++ show n):l) $ deriveInd f2
  return $ Discharge ("a"++ show n) (Just f1) f3

deriveInd (In m s) = do
  env <- ask
  let n:t = env
      sp = Inst (SimpCmp (PVar n)) (spine s)
      l = map (\ x -> PVar x) t
      r = foldr helper sp l
  return r
  where helper a sp = MP sp a
        spine (PVar x) = PVar x
        spine (SApp t1 t) = spine t1
        spine (TApp t1 t) = spine t1

test11 = Forall "C" (Imply (In (PVar "z") (PVar "C")) (Imply (Forall "y" (Imply (In (PVar "y") (PVar "C")) (In (App (PVar "s") (PVar "y")) (PVar "C")))) (Forall "m" (Imply (In (PVar "m") (PVar "Nat")) (In (PVar "m") (PVar "C"))))))
