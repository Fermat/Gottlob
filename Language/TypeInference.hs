module Language.TypeInference where
import qualified Data.Map as M
import qualified Data.Set as S
import Language.Syntax
import Control.Applicative hiding (empty)
import Control.Monad.State.Lazy
import Control.Monad.Identity
import Control.Monad.Reader
import Data.Char

type Constraints = [(EType, EType)]

type InfCxt a = StateT Int (StateT [(VName, EType)] Identity) a

infer :: PreTerm -> InfCxt (EType, Constraints)
infer (PVar x) = do
  m <- lift get
  case lookup x m of
    Just a -> return (a, [])
    Nothing -> 
      if (isUpper $ head x) then do
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

test1 = 
  let s = runIdentity $ runStateT (runStateT (infer $ TApp (SApp (PVar "Vec") (PVar "U")) (PVar "n")) 0) []
      (t,c) = (fst . fst) s
      def = snd s in
  putStrLn $ show def


-- test2 = do
--  s <- runStateT (runStateT (infer $ PSApp (PVar "Vec") (PMApp (PVar "U") (PVar "n"))) 0) []
--  putStrLn $ show s

-- single step solving, the order matters!
step :: Constraints -> Constraints
step ((EVar x,a):l) =
      if x `S.member` (vars a) then ((EVar x,a):l)
      else if x `S.member` (lVars l) then
             (EVar x,a):(map (\ z -> (sub a x (fst z),sub a x (snd z))) l)
           else ((EVar x,a):l)

step ((a1, EVar x):l) =
  case a1 of
    EVar y ->
      (a1, EVar x):l
    _ -> if x `S.member` (vars a1) then
           (a1, EVar x):l
         else (EVar x, a1):l

step ((To a1 a2, To b1 b2):l) =
  (a1, b1):(a2,b2):l

step ((a1, a2):l) =  if a1 == a2 then l
                      else (a1, a2):l

lVars :: Constraints -> S.Set VName
lVars [] = S.empty
lVars ((a1,a2):l) =
  S.union (S.union (vars a1) (vars a2)) (lVars l)

-- man, this is so cool  
solve :: Constraints -> Int -> Constraints
solve l n | n == length l = l
          |  n /= length l =
            let l0 = step l
            in
             if l == l0 then
               let l1 = (tail l ++ [head l])
               in solve l1 (n+1)
             else solve l0 0

isSolvable :: Constraints -> Int -> Bool
 -- for a relax notion of solvable, use:  x `S.member` (S.union (lVars l) (vars t))
isSolvable [] _ = True
isSolvable ((EVar x, t):l) n | n /= length l +1 = if S.null $ vars t 
                                                  then isSolvable (l++[(EVar x, t)]) (n+1)
                                                  else False
                             | n == length l +1 = True
isSolvable _ _ = False
-- example by Prof. Stump's
multiSub :: Constraints -> EType -> EType
multiSub c (EVar x) =
  let c1 = map (\ ((EVar y), t) -> (y, t)) c
  in
   case lookup x c1 of
     Nothing -> EVar x
     Just b -> b
multiSub c Form = Form
multiSub c Ind = Ind
multiSub c (To a b) = To (multiSub c a) (multiSub c b)

test3 = solve
        [(To (To (EVar "Y") (EVar "Z")) (EVar "W"),To (EVar "X") (EVar "X")),(EVar "W",To (EVar "A") (EVar "A"))] 0

             


