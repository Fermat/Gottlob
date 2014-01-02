module Language.Eval where
import Language.Syntax
import Language.Monad
import Control.Monad.State.Lazy
import qualified Data.Map as M
import Control.Monad.Reader

step :: Meta -> Global Meta       
step (In t2 (Iota x t t1)) = do
  let a = fst $ runState (subst t2 (MVar x t) t1) 0 
  return a

step (In t2 t1) = do
  a <- step t1
  return $ In t2 a

step (Iota x c t) = do
  a <- step t
  return $ Iota x c a

step (MVar x t1) = do
  e <- ask
  let a = M.lookup x (def e)
  case a of
    Nothing -> return $ MVar x t1
    Just (et, t) -> return t

reduce :: Meta -> Global Meta       
reduce t = do
  m <- step t
  n <- step m
  if m == n then return m
    else reduce m

          
