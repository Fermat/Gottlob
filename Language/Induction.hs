module Language.Induction (runDerive, getInd) where
import Language.Syntax
import Language.PrettyPrint
import Control.Monad.Reader
import Control.Monad.Identity
import Control.Monad.State.Lazy


import Data.List
import Data.Char

-- take in a inductive set def and return


-- rename a set var in formula
rename :: PreTerm -> PreTerm -> PreTerm -> PreTerm
rename (PVar y) (PVar x) (PVar z) = if x == z then PVar y else PVar z

rename (PVar y) (PVar x) (Forall z f) =
  if x == z then Forall y $ rename (PVar y) (PVar x) f
  else Forall z $ rename (PVar y) (PVar x) f

rename (PVar y) (PVar x) (Iota z f) =
  if x == z then Forall y $ rename (PVar y) (PVar x) f
  else Iota z $ rename (PVar y) (PVar x) f

rename (PVar y) (PVar x) (Imply f1 f2) =
  let a1 = rename (PVar y) (PVar x) f1
      a2 = rename (PVar y) (PVar x) f2 in
  Imply a1 a2

rename (PVar y) (PVar x) (In f1 f2) =
  let a2 = rename (PVar y) (PVar x) f2 in
  In f1 a2

rename (PVar y) (PVar x) (SApp f1 f2) =
  let a1 = rename (PVar y) (PVar x) f1
      a2 = rename (PVar y) (PVar x) f2 in
  SApp a1 a2

rename (PVar y) (PVar x) (TApp f1 f2) =
  let a1 = rename (PVar y) (PVar x) f1 in
  TApp a1 f2

tailAppend x (Imply f1 f2) y = Imply f1 (tailAppend x f2 y)
tailAppend x f2 y=
  Forall x (Imply (rename (PVar $ y++ show 1) (PVar y) f2) f2)
-- tailAppend x f = error $ show f

-- change (In x (PVar y)) = In x (PVar (y++show 1))
-- change (In x (SApp (PVar y) s)) = In x (SApp (PVar (y++show 1)) s)
-- change (In x (TApp (PVar y) s)) = In x (TApp (PVar (y++show 1)) s)
-- change (In x (SApp s1 s2)) = 
-- set to ind principle
-- set -> formula
toFormula :: PreTerm -> PreTerm

toFormula (Iota x (Forall y p)) = Forall y $ tailAppend x p y
toFormula (Iota x p) = Forall x (toFormula p)
--toFormula p = error $ show p
-- getInduction prin from a set
getInd :: PreTerm -> PreTerm
getInd t =
  let
    name@(PVar n) = getName t
    f = toFormula t
    p = rename (PVar $ n ++ show 0) name f
    p1 = rename name (PVar $ n ++ show 1) p in
  p1

type Env a = ReaderT [VName] (StateT Int Identity) a
-- runDerive take in a inductive set and return a proof of its ind
runDerive :: PreTerm -> PreTerm
runDerive t =
  fst $ runIdentity $ runStateT (runReaderT (deriveInd t) []) 0

getName (Iota x (Forall z f)) = PVar z
getName (Iota x f) = getName f
 

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
      sp = Inst (Cmp (PVar n)) (spine s)
      l = map (\ x -> PVar x) t
      r = foldr helper sp l
  return r
  where helper a sp = MP sp (Cmp a)
        spine (PVar x) = PVar x
        spine (SApp t1 t) = spine t1
        spine (TApp t1 t) = spine t1

test11 = Forall "C" (Imply (In (PVar "z") (PVar "C")) (Imply (Forall "y" (Imply (In (PVar "y") (PVar "C")) (In (App (PVar "s") (PVar "y")) (PVar "C")))) (Forall "m" (Imply (In (PVar "m") (PVar "Nat")) (In (PVar "m") (PVar "C"))))))

test12 = Iota "m" (Forall "Nat" (Imply (In (PVar "z") (PVar "Nat")) (Imply (Forall "y" (Imply (In (PVar "y") (PVar "Nat")) (In (App (PVar "s") (PVar "y")) (PVar "Nat")))) (In (PVar "m") (PVar "Nat")))))
