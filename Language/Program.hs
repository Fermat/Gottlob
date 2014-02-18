module Language.Program
       (progTerm, toSet, toScott) where
import Language.Syntax
import Data.List
import Data.Char

-- Translating Program to meta term
progTerm :: Prog -> PreTerm
progTerm (Name n) = PVar n
progTerm (Applica p1 p2) = App (progTerm p1) (progTerm p2)
progTerm (Abs l p) = constrAbs l (progTerm p)
progTerm (Match v l) = appBranch l (progTerm v)
progTerm (ProgPos pos p) = Pos pos (progTerm p)

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






