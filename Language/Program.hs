module Language.Program where
import Language.Syntax
import Data.List
{-
constrEType :: [EType] -> EType
constrEType (x:l) = To x (constrEType l)
constrEType [] = To Ind Form

constrApp :: [Meta] -> Meta -> Meta
constrApp [] t = t
constrApp (x:l) t = constrApp l (In x t)

-- Translating Formal-Type to Set
interp :: FType -> Meta
interp (FVar x t) = MVar x t
interp (Base x l) =
  constrApp (map (helper.fst) l) (MVar x (constrEType (map snd l)))
  where helper a =
          case a of
            FT tf-> interp tf
            TM t -> t
          
interp (Arrow t1 t2) =
  Iota "f" Ind (Forall "x" Ind (Imply (In (MVar "x" Ind) (interp t1)) (In (In (MVar "x" Ind) (MVar "f" Ind)) (interp t2))))

interp (Pi x t1 t2) =
  Iota "f" Ind (Forall x Ind (Imply (In (MVar x Ind) (interp t1)) (In (In (MVar x Ind) (MVar "f" Ind)) (interp t2))))

constrIota :: [(VName, EType)] -> Meta -> Meta
constrIota [] m = m
constrIota ((x,t):l) m = Iota x t (constrIota l m)

constrBranches :: [(VName,FType)] -> Meta -> Meta
constrBranches ((x,t):l) m =
  Imply (In (MVar x Ind) (interp t)) (constrBranches l m)
constrBranches [] m = m

toSet :: Datatype -> (VName, Meta)
toSet (Data d l branches) =
  let t = constrEType (map snd l)
      final = (In (MVar "x" Ind) (constrApp (map (\ x -> (MVar (fst x) (snd x))) l) (MVar d t)))
      body = Iota "x" Ind (Forall d t (constrBranches branches final)) in
  (d, constrIota l body)

arity :: FType -> Int
arity (Arrow _ t) = 1 + (arity t)
arity (Pi _ _ t) = 1 + (arity t)
arity _ = 0

args :: VName -> Int -> Meta -> Meta
args a 0 t = t
args a n t = args a (n-1) (In (MVar (a++ show n) Ind) t)

abstr :: VName -> Int -> Meta -> Meta
abstr a 0 t = t
abstr a n t = Iota (a++ show n) Ind (abstr a (n-1) t)

getConstr :: Datatype -> [VName]
getConstr (Data _ _ l)  = map fst l


-- scottization
toScott :: Datatype -> Datatype  -> [(VName, Meta)]
toScott l (Data d _ []) = []
toScott l (Data d _ ((c,t):xs)) =
  let n = arity t
      a = args "a" n (MVar c Ind)
      b = constr (getConstr l) a
      e = abstr "a" n b in
  (c, e):(toScott l (Data d [] xs))

app :: Meta -> Meta -> Meta
app m1 m2 = In m2 m1

-}
-- Translating Program to meta term
progTerm :: Prog -> PreTerm
progTerm (Name n) = PVar n 
progTerm (Applica p l) =
  foldl' (\ z x -> App z (progTerm x)) (progTerm p) l 
progTerm (Abs l p) = constr l (progTerm p)
progTerm (Match v l) = appBranch l (progTerm v)

constr :: [VName] -> PreTerm -> PreTerm
constr [] t = t
constr (x:xs) t = Lambda x (constr xs t)

appBranch :: [(VName, [VName], Prog)] -> PreTerm -> PreTerm
appBranch [] m = m
appBranch ((v,l,p):xs) m = App m (constr l (progTerm p))




