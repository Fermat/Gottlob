module Language.Eval (reduce) where
import Language.Syntax
import Language.Monad
import Language.PrettyPrint

import Control.Monad.State.Lazy
import Control.Monad.Reader
import Control.Monad.Error

import qualified Data.Map as M

step :: PreTerm -> Global PreTerm
step (App (Lambda x t1) t2 ) = return $ runSubst t2 (PVar x) t1

step (App t1 t2) = step t1 >>= \ a -> return $ App a t2

step (Lambda x t) = step t >>= \a -> return $ Lambda x a

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
  if m == n then return m else reduce m

          
