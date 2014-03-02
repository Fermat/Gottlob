module Language.Program
       (progTerm, toSet, toScott, runToProof) where
import Language.Syntax
import Control.Monad.Reader
import Data.List
import Data.Char

-- Translating Program to meta term
progTerm :: Prog -> PreTerm
progTerm (Name n) = PVar n
progTerm (Applica p1 p2) = App (progTerm p1) (progTerm p2)
progTerm (Abs l p) = constrAbs l (progTerm p)
progTerm (Match v l) = appBranch l (progTerm v)
progTerm (ProgPos pos p) = Pos pos (progTerm p)
progTerm (Let l p) = substList (helper l) (progTerm p)
  where helper l = map (\ (x, t) -> (PVar x, progTerm t)) l
        substList [] t = t
        substList ((x, t1):xs) t = substList xs (runSubst t1 x t)
progTerm (TMP p1 p2) = MP (progTerm p1) (progTerm p2)
progTerm (TInst p1 p2) = Inst (progTerm p1) (progTerm p2)
progTerm (TUG x p2) = UG x (progTerm p2)
progTerm (TCmp p1) = Cmp (progTerm p1)
progTerm (TBeta p1) = Beta (progTerm p1)
progTerm (TInvCmp p1 p2) = InvCmp (progTerm p1) (progTerm p2)
progTerm (TInvBeta p1 p2) = InvBeta (progTerm p1) (progTerm p2)
progTerm (TDischarge x p1 p2) = Discharge x (Just $ progTerm p1) (progTerm p2)
progTerm (TPLam x p2) = PLam x (progTerm p2)
progTerm (TPApp p1 p2) = PApp (progTerm p1) (progTerm p2)
progTerm (TPFApp p1 p2) = PFApp (progTerm p1) (progTerm p2)



constrAbs :: [VName] -> PreTerm -> PreTerm
constrAbs l t = foldr (\ x z -> Lambda x z) t l

appBranch :: [(VName, [VName], Prog)] -> PreTerm -> PreTerm
appBranch l m = foldl' (\ z x -> App z (helper x)) m l
  where helper (v,l,p) = constrAbs l (progTerm p)

-- Translating Formal-Type to Set
interp :: FType -> PreTerm
interp (FVar x) = PVar x
interp (FCons x l) =
  foldl' helper (PVar x) l 
  where helper z (ArgType tf) = SApp z $ interp tf
        helper z (ArgProg t) = TApp z $ progTerm t

interp (Arrow t1 t2) = template "x" (interp t1) (interp t2)
interp (Pi x t1 t2) = template x (interp t1) (interp t2)
interp (FTPos pos ftype) = Pos pos (interp ftype)

template x p1 p2 = Iota "f" (Forall x
                             (Imply (In (PVar x) p1)
                              (In (App (PVar "f") (PVar x)) p2)))
  
-- Translate data type decl to set

-- Iota x1. (Iota x2. ...t)
constrIota :: [VName] -> PreTerm -> PreTerm
constrIota l t = foldr (\ x z -> Iota x z) t l

-- A1 -> (A2 -> ... m)
constrBranches :: [(VName,FType)] -> PreTerm -> PreTerm
constrBranches l m =
  foldr (\ x z -> Imply (helper x) z) m l 
  where helper (x,t) = In (PVar x) (interp t)

toSet :: Datatype -> (VName, PreTerm)
toSet (Data d l branches) =
  let final = In (PVar "x") (interp (FCons d (map helper l)))
      body = Iota "x" (Forall d (constrBranches branches final)) in
  (d, constrIota l body)
  where helper x = if (isUpper $ head x)
                   then ArgType (FVar x)
                   else ArgProg (Name x)

arity :: FType -> Int
arity (Arrow _ t) = 1 + (arity t)
arity (Pi _ _ t) = 1 + (arity t)
arity (FTPos p t) = arity t
arity _ = 0

args :: VName -> Int -> PreTerm -> PreTerm
args a 0 t = t
args a n t = args a (n-1) (App t (PVar (a++ show n)))

abstr :: VName -> Int -> PreTerm -> PreTerm
abstr a 0 t = t
abstr a n t = Lambda (a++ show n) (abstr a (n-1) t)

-- scottization, get the scott encoded constructors
toScott :: Datatype -> [(VName, PreTerm)]
toScott (Data d l cons) =
  let l1 = map fst cons in
  map (helper l1) cons
  where helper l1 (c, t) =
          let n = arity t
              a = args "a" n (PVar c)
              b = constrAbs l1 a
              e = abstr "a" n b in (c, e)
-- a small test on nat
-- nat = Data "Nat" [] [("z", FVar "Nat"), ("s", Arrow (FVar "Nat") (FVar "Nat"))]      

-- translating proof scripts to proof.
runToProof ::ProofScripts -> PreTerm
runToProof ps = runReader (toProof ps) []

toProof :: ProofScripts -> Reader [(VName, PreTerm)] PreTerm
toProof ((n,Right p,f):[]) = annotate p
toProof ((n,Left (Assume x), Just f):xs) = local (\ y -> (x, f):y) (toProof xs)
toProof ((n,Right p, f):xs) = toProof $ substPL p n xs
  where substPL p n xs = map helper xs
        helper (n1, Right p1, f1) = (n1 , Right $ naiveSub p (PVar n) p1 , f1)
        helper (n1, Left a, f1) = (n1 , Left a , f1)

annotate :: PreTerm -> Reader [(VName, PreTerm)] PreTerm
annotate (Discharge x Nothing p) = do
  l <- ask
  case lookup x l of
    Nothing -> do
      p1 <- annotate p
      return $ Discharge x Nothing p1
    Just f -> do
      p1 <- annotate p
      return $ Discharge x (Just f) p1

annotate (Discharge x (Just f) p) = do
  p1 <- annotate p
  return $ Discharge x (Just f) p1
  
annotate (PVar p) = return $ PVar p
annotate (MP p1 p2) = do
  p3 <- annotate p1
  p4 <- annotate p2
  return $ MP p3 p4
annotate (Inst p1 t) = do
  p3 <- annotate p1
  return $ Inst p3 t

annotate (UG x p1) = do
  p3 <- annotate p1
  return $ UG x p3

annotate (Cmp p1) = do
  p3 <- annotate p1
  return $ Cmp p3

annotate (Beta p1) = do
  p3 <- annotate p1
  return $ Beta p3

annotate (InvCmp p1 t) = do
  p3 <- annotate p1
  return $ InvCmp p3 t

annotate (InvBeta p1 t) = do
  p3 <- annotate p1
  return $ InvBeta p3 t

annotate (PLam x p1) = do
  p3 <- annotate p1
  return $ PLam x p3

annotate (PApp p1 p2) = do
  p3 <- annotate p1
  p4 <- annotate p2
  return $ PApp p3 p4

annotate (PFApp p1 t) = do
  p3 <- annotate p1
  return $ PFApp p3 t
annotate (Pos pos p1) = annotate p1



                 





