module TypeInference where
import qualified Data.Map as M
import qualified Data.Set as S
import Language.Syntax
import Control.Monad.State.Lazy
import Control.Monad.Identity
import Control.Monad.Reader
import Data.Char
type Constraints = [(EType, EType)]

type Global a = StateT Int (ReaderT [(VName, EType)] Identity) a

infer :: PreMeta -> Global (EType, Constraints)
infer (PVar x) = do
  m <- ask
  case lookup x m of
    Just a -> return (a, [])
    Nothing -> 
      if (isUpper $ head x) then do
        n <- get
        modify (+1)
        return (EVar $ "X"++ show n, [])
      else return (Ind, [])

infer (PIn p1 p2) = do
  (a1, c1) <- infer p1 
  (a2, c2) <- infer p2
  return (Form, (a1, Ind):(a2, To Ind Form):(c1 ++ c2)) 
  
infer (PApp p1 p2) = do
  (a1, c1) <- infer p1 
  (a2, c2) <- infer p2 
  n <- get
  modify (+1)
  return (EVar $ "X"++ show n, (a1, To a2 (EVar $ "X"++ show n)):(c1 ++ c2)) 

infer (PIota x t) = 
  if (isUpper $ head x) then do
    n <- get
    modify (+1)
    (a, c) <- local (\ y -> (x, (EVar $ "X" ++ show n)): y) (infer t)
    return (To (EVar $ "X" ++ show n) a,c)
  else do
    (a, c) <- local (\ y -> (x, Ind): y) (infer t)
    return (To Ind a,c)

infer (PForall x t) = 
  if (isUpper $ head x) then do
    n <- get
    modify (+1)
    (a, c) <- local (\ y ->  (x, (EVar $ "X" ++ show n)): y) (infer t)
    return (Form,(a, Form):c)
  else do
    (a, c) <- local (\ y -> (x ,Ind): y) (infer t)
    return (Form,(a, Form):c)

infer (PImply p1 p2) = do
  (a1, c1) <- infer p1 
  (a2, c2) <- infer p2 
  return (Form, (a2, Form):(a1, Form):(c1 ++ c2)) 

-- solve :: Constraints -> Constraints

