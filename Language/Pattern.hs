module Language.Pattern(match, Equation, Pattern(..), partition) where
import Language.Syntax
import Language.PrettyPrint
import Text.Parsec
import Text.Parsec.Pos
import Data.List hiding(partition)
import Debug.Trace
-- This file implement(almost the same) Wadler's pattern matching
-- compiler found at section 5.3 in SPJ's
-- the implementation of functional programming language
-- during preprocessing,
-- a group of PatternDecl get analyzed and
-- transformed to Definitions, and filling
-- missing constructor by adding extra
-- equation: ([Cons c x1..xn], error)

data Pattern = Var VName
             | Cons VName [Pattern]
             deriving Show
                      
type Equation = ([Pattern], Prog)
-- data Definition = Def VName [Equation]
--                 deriving Show

isVar :: Equation -> Bool
isVar (Var x:ps,e) = True
isVar (Cons x xs : ps,e) = False

isCon :: Equation -> Bool
isCon e = not $ isVar e

getCon (Cons c ps1:ps, e) = c

constructors :: VName -> [Decl] -> [VName]
constructors v ((DataDecl pos (Data name params cons) b):l) =
  case lookup v cons of
    Just _ -> map (\ x -> fst x) cons
    Nothing -> constructors v l

constructors v (x:l) = constructors v l
constructors v [] = error $ "can't find data construtor " ++ show v

arity :: VName -> [Decl] -> Int
arity v ((DataDecl pos (Data name params cons) b):l) =
  case lookup v cons of
    Just f -> farity f
    Nothing -> arity v l
arity v (x:l) = arity v l
arity v [] = error $ "can't find arity for " ++ show v


partition f [] = []
partition f (x:[]) = [[x]]
partition f (x:x1:xs) | f x == f x1 = tack x (partition f (x1:xs))
                      | otherwise = [x]: partition f (x1:xs)
  where tack x xss = (x : head xss) : tail xss
        
match :: VName -> [Decl] -> Int -> [VName] -> [Equation] -> Prog -> Prog
match name env k [] qs def =
  let p = [e | ([], e) <- qs] in -- trace ("spit p "++ show p ++ show qs ++ show def) (head p)
  if null p then def else head p -- trace ("nonempty head") (head p)
  --foldr Applica def [e | ([], e) <- qs]
--  if null qs then (Name "Error") else let ([], p) = head qs in p
match name env k (u:us) qs def = foldr (matchVarCon name env k (u:us)) def (partition isVar qs)

matchVarCon name env k us qs def | isVar $ head qs = matchVar name env k us qs def
matchVarCon name env k us qs def | otherwise = matchCon name env k us qs def

matchVar name env k (u:us) qs def = match name env k us [(ps, replace u v e) | (Var v : ps, e) <- qs] def

matchCon name env k (u:us) qs def =
  Match (Name u) [matchClause name env c k (u:us) (choose c qs) def | c <- cs]
  where cs = constructors (getCon $ head qs) env
        
matchClause name env c k (u:us) qs def =
  let k' = arity c env in
  (c, map (\x -> Name x) (us' k'), match name env (k'+ k) ((us' k') ++ us) [(ps' ++ ps, e) | (Cons c ps' : ps, e) <- qs] def )
  where
    us' q = [makeVar name (i + k) | i <- [1..q]]
    makeVar n l = n ++ show l

choose c qs = [q | q <- qs, getCon q == c]

-- the naive replace will be replace by capture avoiding subst later.
replace y x (Name z) =
  if x == z then Name y else Name z

replace y x (ProgPos _ p) = replace y x p

replace y x (Applica p1 p2) =
  let a1 = replace y x p1
      a2 = replace y x p2 in
  Applica a1 a2

replace y x (Abs xs p2) =
  let a1 = replace y x p2 in
  Abs xs a1 

replace y x (Match p ls) =
  let a = replace y x p
      ls' = subb y x ls in
  Match a ls'
  where subb y x [] = []
        subb y x ((c,ps,p):ls) =
          (c, ps, replace y x p): subb y x ls
--        subb' y x ps = map (\ z -> if z == x then y else z) ps

replace y x (If p0 p1 p2) =
  let a0 = replace y x p0
      a1 = replace y x p1
      a2 = replace y x p2 in
  If a0 a1 a2

decl = Data "Nat" [] [("z",FVar "Nat"),("s",Arrow (FVar "Nat") (FVar "Nat"))]
eqs = [([(Cons "s" [(Var "n'")]),Var "m"],
                                          ((Applica (Name "s") ((Applica (Applica (Name "add") (Name "n'")) (Name "m")))))), ([Cons "z" [],Var "m"], (Name "m"))]

eqs1 = [([Var "n",Cons "s"[Var "m"]],
        ((Applica (Name "s") ((Applica (Applica (Name "add") (Name "n'")) (Name "m"))))))]


test112 = show $ match "_u" [DataDecl (newPos "ha" 1 1) decl True] 2 ["_u1", "_u2"] eqs (Name "Error")

test13 = disp $ match "_u" [DataDecl (newPos "ha" 1 1) decl True] 2 ["_u1", "_u2"] eqs1 (Name "Error")
