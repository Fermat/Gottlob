module Language.Eval where
import Language.Syntax
import Language.Monad
import Control.Monad.State.Lazy
import qualified Data.Map as M
reduce :: Meta -> PCMonad Meta       
reduce (MVar x t) = do
  e <- get
  let a = M.lookup x (def e)
  case a of
    Nothing -> return $ Right $ MVar x t
    Just t -> reduce t

reduce (In t2 (Iota x t t1)) = do
  let a = fst $ runState (subst t2 (MVar x t) t1) 0 
  reduce a

reduce (In t1 (MVar x t)) = do
  e <- get
  let a = M.lookup x (def e)
  case a of
    Nothing -> return $ Right $ In t1 (MVar x t)
    Just b -> reduce (In t1 b)

reduce (In t (In t1 (MVar x t2))) = do
  e <- get
  let a = M.lookup x (def e)
  case a of
    Nothing -> return $ Right $ In t (In t1 (MVar x t2))
    Just b -> do
      Right c <- reduce (In t1 b)
      reduce (In t c)
          
reduce (In t2 t1) = do
  Right a <- reduce t1
  reduce $ In t2 a

reduce (Iota x c t) = do
  Right a <- reduce t
  return $ Right $ Iota x c a
