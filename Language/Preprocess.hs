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
import qualified Data.Set as S
-- process parsing data 
checkDefs :: Module -> IO (Either String Env)
checkDefs (Module mod l) = do
 a <- runErrorT $ runStateT (runStateT (runGlobal (process l)) emptyEnv) emptyPrfEnv
 case a of
   Left e -> return $ Left e
   Right b -> return $ Right ((snd.fst) b)
   
process :: [Decl] -> Global ()
process [] = return ()
process((FormOperatorDecl _ _ _):l) = process l
process((SpecialOperatorDecl _ _ _):l) = process l
process((ProgOperatorDecl _ _ _):l) = process l
process ((ProgDecl x p):l) = do
  st <- get
  put $ extendProgDef x (progTerm p) st
  process l

process ((DataDecl d):l) = 
  let progs = toScott d d   
      sd = toSet d in
  do
    wellDefined $ snd sd
      -- get constraints and type from type inference, providing the current set-etype info
    state <- get
    let s = runIdentity $ runStateT (runStateT (infer $ snd sd) 0) (map (\ x -> (fst x, (snd . snd) x)) (M.toList $ setDef state))
        (t,c) = (fst. fst) s
        def = snd s
        res = solve c 0 in
      if isSolvable res 0 then do
        let s1 = extendSetDef (fst sd) (snd sd) (multiSub res t) state
            s3 = foldl' (\ z x -> extendProgDef (fst x) (snd x) z) s1 progs in
          put s3
      else throwError ("Illformed/Unsolvable set def for data type "++ show res ++
                    ":defs:" ++ show def ++ ":set: " ++ show sd)
    process l

process ((SetDecl x set):l) = do
  wellDefined set
  state <- get
  let s = runIdentity $ runStateT (runStateT (infer set) 0) (map (\ x -> (fst x, (snd . snd) x)) (M.toList $ setDef state))
      (t,c) = (fst. fst) s
      def = snd s
      res = solve c 0 in
    if isSolvable res 0 then do
      let s1 = extendSetDef x set (multiSub res t) state
        in
        put s1
    else throwError ("Illformed/Unsolvable set def for data type "++ show res ++
                    ":defs:" ++ show def ++ ":set: ")
  process l

wellDefined :: PreTerm -> Global ()
wellDefined t = do
  env <- get
  let l = S.toList $ fVar t 
      rs = map (\ x -> helper x env) l
      fs = [c | c <- rs, fst c == False]
      ffs = map (\ x -> snd x) fs in
    if null ffs then return ()
    else throwError $ "undefine set variables: " ++ (show $ unwords ffs)
  where helper x env =
          case M.lookup x (setDef env) of
            Just a -> (True, x)
            _ -> (False, x)
