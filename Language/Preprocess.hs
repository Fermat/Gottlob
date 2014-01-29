module Language.Preprocess where
import Language.TypeInference
import Language.Syntax
import Language.Program
import Language.Monad
import Control.Monad.Identity
import Control.Monad.State
import Data.List
import Control.Monad.Error
import qualified Data.Map as M
-- process parsing data 
checkDefs :: Module -> Global ()
checkDefs (Module mod l) = process l

process :: [Decl] -> Global ()
process ((ProgDecl x p):l) = do
  st <- get
  put $ extendProgDef x (progTerm p) st

process ((DataDecl d):l) = do
  state <- get
  let progs = toScott d d   
      sd = toSet d
      -- get constraints and type from type inference, providing the current set-etype info
      s = runIdentity $ runStateT (runStateT (infer $ snd sd) 0) (map (\ x -> (fst x, (snd . snd) x)) (M.toList $ setDef state))
      (t,c) = (fst. fst) s
--      def = snd s
      res = solve ((t, To Ind Form):c) 0 in
    if isSolvable res 0 then do
  --  st <- get
      let s1 = extendSetDef (fst sd) (snd sd) (To Ind Form) state
          s3 = foldl' (\ z x -> extendProgDef (fst x) (snd x) z) s1 progs in
        put s3
    else throwError ("Illformed set def for data type"++ show d)
        

