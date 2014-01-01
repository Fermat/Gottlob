module Language.Eval where
import Language.Syntax
import Language.Monad
import Control.Monad.State.Lazy
import qualified Data.Map as M
import Control.Monad.Reader

reduce :: Meta -> Global Meta       
reduce (MVar x) = do
  e <- ask
  let a = M.lookup x (def e)
  case a of
    Nothing -> return $ MVar x
    Just t -> reduce t

reduce (In t2 (Iota x t t1)) = do
  let a = fst $ runState (subst t2 (MVar x) t1) 0 
  reduce a

reduce (In t1 (MVar x)) = do
  e <- ask
  let a = M.lookup x (def e)
  case a of
    Nothing -> return $ In t1 (MVar x)
    Just b -> reduce (In t1 b)

reduce (In t (In t1 (MVar x))) = do
  e <- ask
  let a = M.lookup x (def e)
  case a of
    Nothing -> return $ In t (In t1 (MVar x))
    Just b -> do
      c <- reduce (In t1 b)
      reduce (In t c)
          
reduce (In t2 t1) = do
  a <- reduce t1
  reduce $ In t2 a

reduce (Iota x c t) = do
  a <- reduce t
  return $ Iota x c a
