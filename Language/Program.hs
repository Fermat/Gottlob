module Language.Program
       (progTerm, toSet, toScott) where
import Language.Syntax
import Language.Pattern
import Text.PrettyPrint
import Control.Monad.Reader
import Data.List
import Data.Char

-- Translating Flat Program to meta term

progTerm :: Prog -> PreTerm
progTerm (Name n) = PVar n
progTerm (Applica p1 p2) = 
  let a1 = progTerm p1
      a2 = progTerm p2 in App a1 a2

progTerm (Abs l p) =
  let a = progTerm p in constrAbs l a
                        
progTerm (Match v l) =
  let a = progTerm v in appBranch l a
                        
progTerm (ProgPos pos p) =
  let a = progTerm p in Pos pos a

progTerm (Let l p) = 
  let a = progTerm p in
  substList (helper l) a
  where helper l = map (\ (x, t) -> (PVar x, progTerm t)) l
        substList [] t = t
        substList ((x, t1):xs) t = substList xs (runSubst t1 x t)

progTerm (TForall x p) =
  let a = progTerm p in Forall x a

progTerm (TImply f1 f2) =
  let a1 = progTerm f1
      a2 = progTerm f2 in Imply a1 a2

progTerm (TIota x p) =
  let a = progTerm p in Iota x a

progTerm (TIn f1 f2) =
  let a1 = progTerm f1
      a2 = progTerm f2 in In a1 a2

progTerm (TSApp f1 f2) =
  let a1 = progTerm f1
      a2 = progTerm f2 in SApp a1 a2

progTerm (TSTApp f1 f2) =
  let a1 = progTerm f1
      a2 = progTerm f2 in TApp a1 a2
  
progTerm (TMP p1 p2) = 
  let a1 = progTerm p1
      a2 = progTerm p2 in MP a1 a2
  
progTerm (TInst p1 p2) =
  let a = progTerm p1
      a2 = progTerm p2
  in Inst a a2
                         
progTerm (TUG x p2) =
  let a = progTerm p2 in UG x a
progTerm (TCmp p1) =
  let a = progTerm p1 in Cmp a

progTerm (TBeta p1) =
  let a = progTerm p1 in Beta a

progTerm (TInvCmp p1 p2) =
  let a = progTerm p1
      a2 = progTerm p2
  in InvCmp a a2
progTerm (TInvBeta p1 p2) =
  let a = progTerm p1
      a2 = progTerm p2
  in InvBeta a a2
progTerm (TDischarge x p1 p2) =
  case p1 of
    Nothing -> 
      let a = progTerm p2 in Discharge x Nothing a
    Just t ->
      let a0 = progTerm t
          a = progTerm p2
      in Discharge x (Just a0) a

progTerm (AppPre p1 p2) =
  let a = progTerm p1
      a2 = progTerm p2 in App a a2

progTerm (If c p1 p2) = 
  let c1 = progTerm c
      a1 = progTerm p1
      a2 = progTerm p2
  in App (App (App iff c1) a1 ) a2
{-
  progTerm (Name n) = PVar n
progTerm (Applica p1 p2) = do
  a1 <- progTerm p1
  a2 <- progTerm p2
  return $ App a1 a2

progTerm (Abs l p) = progTerm p >>= \ a -> return $ constrAbs l a 
progTerm (Match v l) = progTerm v >>= \ a -> appBranch l a
progTerm (ProgPos pos p) = progTerm p >>= \ a -> return $ Pos pos a

-- progTerm (Let l p) = do
--   a <- progTerm p
--   return $ substList (helper l) a
--   where helper l = map (\ (x, t) -> (PVar x, progTerm t)) l
--         substList [] t = t
--         substList ((x, t1):xs) t = substList xs (runSubst t1 x t)
        
progTerm (TMP p1 p2) = do
  a1 <- progTerm p1
  a2 <- progTerm p2
  return $ MP a1 a2
  
progTerm (TInst p1 p2) = progTerm p1 >>= \a -> return $ Inst a p2
progTerm (TUG x p2) = progTerm p2 >>= \ a -> return $ UG x a
progTerm (TCmp p1) = progTerm p1 >>= \ a -> return $ Cmp a
progTerm (TBeta p1) = progTerm p1 >>= \ a -> return $ Beta a
progTerm (TInvCmp p1 p2) = progTerm p1 >>= \a -> return $ InvCmp a p2
progTerm (TInvBeta p1 p2) = progTerm p1 >>= \ a -> return $ InvBeta a p2
progTerm (TDischarge x p1 p2) = progTerm p2 >>= \a -> return $ Discharge x p1 a
-- progTerm (TPLam x p2) = Lambda x (progTerm p2)
-- progTerm (TPApp p1 p2) = App (progTerm p1) (progTerm p2)
-- progTerm (TPFApp p1 p2) = App (progTerm p1) p2
progTerm (AppPre p1 p2) = progTerm p1 >>= \ a -> return $ App a p2

progTerm (If c p1 p2) = do
  c1 <- progTerm c
  a1 <- progTerm p1
  a2 <- progTerm p2
  return $ App (App (App iff c1) a1 ) a2 -}
-- it is a little ad hoc
iff = Lambda "a" (Lambda "then" (Lambda "else"
                                 (App (App (PVar "a") (PVar "then")) (PVar "else"))))
--progTerm (AppProof p1 p2) = App (progTerm p1) (progTerm p2)

constrAbs :: [VName] -> PreTerm -> PreTerm
constrAbs l t = foldr (\ x z -> Lambda x z) t l

appBranch :: [(VName, [Prog], Prog)] -> PreTerm -> PreTerm
appBranch l m = 
  foldl' (\ z x ->  App z (helper x)) m l
  where
    helper (v,l,p) = 
      let l1 = map (\ (Name x) -> x) l
          a = progTerm p in
      constrAbs l1 a 
{-
patProg :: Prog -> ReaderT [Decl] (Either VName) Prog
patProg (Name n) = return $ Name n
patProg (Applica p1 p2) = do
  return $ Applica p1 p2

patProg (Abs l p) = do
  p1 <- patProg p
  return $ Abs l p1

patProg (ProgPos pos p) = patProg p >>= \ a -> return $ ProgPos pos a  

patProg (Match v l) = patProg v >>= \ a -> appBranch l a


toPat :: Prog -> ReaderT [Decl] (Either VName) Pattern 
toPat (Name c) = do
  state <- ask
  if isConstr c state then return $ (Cons c [])
  else return $ (Var c)
toPat (Applica (Name c) b) = do
  state <- ask
  if isConstr c state then
    return $ Cons c (toVar b)
  else fail c
toPat (Applica a b) = do
  (Cons v ls) <- toPat a
  return $ Cons v (ls ++ (toVar b))

toPat (ProgPos pos p) = toPat p

toVar (Name a) = [Var a]
toVar (Applica a b) = (toVar a) ++ (toVar b)

isConstr v ((DataDecl pos (Data name params cons) b):l) =
  case lookup v cons of
    Just _ -> True
    Nothing -> isConstr v l

isConstr v (x:l) = isConstr v l
isConstr v [] = False
-}
-- Translating Formal-Type to Set
interp :: FType -> PreTerm
interp (FVar x) = PVar x
interp (FCons x l) =
  foldl' helper (PVar x) l 
  where helper z (ArgType tf) = SApp z $ interp tf
        helper z (ArgProg t) =
          let t1 = progTerm t in 
          TApp z t1

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
{-
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

annotate (Lambda x t) = do
  p <- annotate t
  return $ Lambda x p 

annotate (App p1 p2) = do
  p3 <- annotate p1
  p4 <- annotate p2
  return $ App p3 p4

annotate (Pos pos p1) = annotate p1
-}



                 





