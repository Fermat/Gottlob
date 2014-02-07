module Language.TypeInference
       (runInference, runSolve, multiSub, isSolvable, Constraints)where
import Language.Syntax

import Control.Applicative hiding (empty)
import Control.Monad.State.Lazy
import Control.Monad.Identity
import Control.Monad.Reader

import Data.Char
import qualified Data.Map as M
import qualified Data.Set as S

type Constraints = [(EType, EType)]

type InfCxt a = StateT Int (StateT [(VName, EType)] Identity) a

runInference :: PreTerm -> [(VName, EType)] -> (EType, Constraints, [(VName, EType)])
runInference p c =
  let s = runIdentity $ runStateT (runStateT (infer p) 0) c
      (t,c1) = (fst. fst) s
      def = snd s in (t,c1,def)

infer :: PreTerm -> InfCxt (EType, Constraints)
infer (Pos _ p) = infer p
infer (PVar x) = do
  m <- lift get
  case lookup x m of
    Just a -> return (a, [])
    Nothing -> 
      if not (isLower $ head x) then do
        n <- get
        modify (+1)
        lift $ modify (\ y -> (x, (EVar $ "X" ++ show n)): y)
        return (EVar $ "X"++ show n, [])
      else return (Ind, [])

infer (In p1 p2) = do
  (a2, c2) <- infer p2
  return (Form, (a2, To Ind Form):c2) 
  
infer (SApp p1 p2) = do
  (a1, c1) <- infer p1 
  (a2, c2) <- infer p2 
  n <- get
  modify (+1)
  return (EVar $ "X"++ show n, (a1, To a2 (EVar $ "X"++ show n)):(c1 ++ c2)) 

infer (TApp p1 p2) = do
  (a1, c1) <- infer p1 
  n <- get
  modify (+1)
  return (EVar $ "X"++ show n, (a1, To Ind (EVar $ "X"++ show n)):c1) 

infer (Iota x t) = 
  if (isUpper $ head x) then do
    n <- get
    modify (+1)
    lift $ modify (\ y -> (x, (EVar $ "X" ++ show n)): y)
    (a, c) <- infer t
    return (To (EVar $ "X" ++ show n) a,c)
  else do
    (a, c) <- infer t
    return (To Ind a,c)

infer (Forall x t) = 
  if (isUpper $ head x) then do
    n <- get
    modify (+1)
    lift $ modify (\ y ->  (x, (EVar $ "X" ++ show n)): y)
    (a, c) <- infer t
    return (Form,(a, Form):c)
  else do
    (a, c) <- infer t
    return (Form,(a, Form):c)

infer (Imply p1 p2) = do
  (a1, c1) <- infer p1 
  (a2, c2) <- infer p2 
  return (Form, (a2, Form):(a1, Form):(c1 ++ c2)) 

infer (Lambda x t) = return (Ind, [])
infer (App t1 t2) = return (Ind, [])
-- test1 = 
--   let s = runIdentity $ runStateT (runStateT (infer $ TApp (SApp (PVar "Vec") (PVar "U")) (PVar "n")) 0) []
--       (t,c) = (fst . fst) s
--       def = snd s in
--   putStrLn $ show def

-- test2 = do
--  s <- runStateT (runStateT (infer $ PSApp (PVar "Vec") (PMApp (PVar "U") (PVar "n"))) 0) []
--  putStrLn $ show s

-- Implementing a Constraints solving algorithm
-- from Prof. Stump's book.
-- single step solving, the order of each case matters!
step :: Constraints -> Constraints
step ((EVar x,a):l) =
  if x `S.member` (vars a) then (EVar x,a):l
  else if x `S.member` (lVars l)
       then (EVar x,a): map helper l
       else (EVar x,a):l
    where helper (z1,z2) = (sub a x z1, sub a x z2)

step ((a1, EVar x):l) = case a1 of
                          EVar y -> (a1, EVar x):l
                          _ -> if x `S.member` (vars a1) then (a1, EVar x):l
                               else (EVar x, a1):l

step ((To a1 a2, To b1 b2):l) = (a1, b1):(a2,b2):l

step ((a1, a2):l) =  if a1 == a2 then l else (a1, a2):l

lVars :: Constraints -> S.Set VName
lVars l = foldr (\ x z -> helper x `S.union` z) S.empty l
  where helper (a1, a2) = vars a1 `S.union` vars a2
        
-- man, this is so cool  
solve :: Constraints -> Int -> Constraints
solve l n | n == length l = l
          |  n /= length l =
            let l0 = step l in
            if l == l0 then solve (tail l ++ [head l]) (n+1)
            else solve l0 0

runSolve l = solve l 0

isSolvable :: Constraints -> Bool
isSolvable l =  null [i | i <- ensure l, i == False]
  where ensure l = map (\ x -> pat x) l
        pat (EVar x, t) = S.null $ vars t
        pat _ = False
        
multiSub :: Constraints -> EType -> EType
multiSub c (EVar x) =
  case lookup (EVar x) c of
    Nothing -> EVar x
    Just b -> b
    
multiSub c Form = Form
multiSub c Ind = Ind
multiSub c (To a b) = To (multiSub c a) (multiSub c b)

-- example by Prof. Stump's
-- test3 = solve
--         [(To (To (EVar "Y") (EVar "Z")) (EVar "W"),To (EVar "X") (EVar "X")),(EVar "W",To (EVar "A") (EVar "A"))] 0

