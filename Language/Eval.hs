module Language.Eval where
import Language.Syntax
import Language.Monad
import Language.PrettyPrint
import Control.Monad.State.Lazy
import qualified Data.Map as M
import Control.Monad.Reader
import Control.Monad.Error

step :: PreTerm -> Global PreTerm
step (App (Lambda x t1) t2 ) = 
  return $ fst $ runState (subst t2 (PVar x) t1) 0 

step (App t1 t2) = do
  a <- step t1
  return $ App a t2

step (Lambda x t) = do
  a <- step t
  return $ Lambda x a

step (PVar x) = do
  e <- get
  case M.lookup x (progDef e) of
    Nothing -> do
      emit $ "continuing reduction with free prog variable" <++> x
      return $ PVar x
    Just t -> return t

step _ = die "Wrong use of eval/reduction."
reduce :: PreTerm -> Global PreTerm
reduce t = do
  m <- step t
  n <- step m
  if m == n then return m
    else reduce m

          
