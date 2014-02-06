module Language.Program where
import Language.Syntax
import Data.List

-- constrEType :: [EType] -> EType
-- constrEType (x:l) = To x (constrEType l)
-- constrEType [] = To Ind Form
  -- constrApp (map helper l) (PVar x)
  -- where helper (ArgType tf) = interp tf
  --       helper (ArgProg t) = progTerm t

-- constrApp :: [PreTerm] -> PreTerm -> PreTerm
-- constrApp [] t = t
-- constrApp (x:l) t = if isTerm x then constrApp l (TApp t x)
--                     else constrApp l (SApp t x)

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
  

{-
constrIota :: [VName] -> PreTerm -> PreTerm
constrIota [] m = m
constrIota (x:l) m = Iota x (constrIota l m)

constrBranches :: [(VName,FType)] -> PreTerm -> PreTerm
constrBranches ((x,t):l) m =
  Imply (In (PVar x) (interp t)) (constrBranches l m)
constrBranches [] m = m

toSet :: Datatype -> (VName, PreTerm)
toSet (Data d l branches) =
  let --t = constrEType (map snd l)
      final = In (PVar "x") (constrApp (map (\ x -> PVar x) l) (PVar d))
      body = Iota "x" (Forall d (constrBranches branches final)) in
  (d, constrIota l body)

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

getConstr :: Datatype -> [VName]
getConstr (Data _ _ l)  = map fst l

-- scottization
toScott :: Datatype -> Datatype  -> [(VName, PreTerm)]
toScott l (Data d _ []) = []
toScott l (Data d _ ((c,t):xs)) =
  let n = arity t
      a = args "a" n (PVar c)
      b = constr (getConstr l) a
      e = abstr "a" n b in
  (c, e):(toScott l (Data d [] xs))
-}
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




