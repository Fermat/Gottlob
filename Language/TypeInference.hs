module TypeInference where
import qualified Data.Map as M
import qualified Data.Set as S
import Language.Syntax
import Control.Monad.State.Lazy
import Control.Monad.Identity
import Data.Char
type Constraints = [(EType, EType)]

type Global a = StateT Int (StateT (M.Map VName EType) Identity) a

getVars :: PreMeta -> S.Set VName
getVars (PVar x) = S.insert x S.empty
getVars (PForall x p) = S.insert x (getVars p)
getVars (PIota x p) = S.insert x (getVars p)
getVars (PImply p1 p2) = S.union (getVars p1) (getVars p2)
getVars (PIn p1 p2) = S.union (getVars p1) (getVars p2)
getVars (PApp p1 p2) = S.union (getVars p1) (getVars p2)

annotate :: [VName] -> Global ()
annotate [] = return ()
annotate (x:l) = do
  helper x
  annotate l
  where helper x = if isLower (head x) then
                     do
                       m <- lift get
                       lift $ put $ M.insert x Ind m
                       return () 
                    else do
                        n <- get
                        m <- lift get
                        case M.lookup x m of
                          Nothing -> do
                            lift $ put $ M.insert x (EVar ("X"++ show n)) m
                            modify (+1)
                          Just _ -> return ()

genConstraints :: PreMeta -> Global Constraints




-- solve :: Constraints -> Constraints

