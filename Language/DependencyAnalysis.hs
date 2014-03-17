module Language.DependencyAnalysis where
import Language.Syntax
import Language.Pattern(partition)
import Language.PrettyPrint
import Data.List hiding(partition)
import qualified Data.Set as S
import Control.Monad.State
import Debug.Trace
consDef :: VName -> [Decl] -> Bool
consDef v ((DataDecl pos (Data name params cons) b):l) =
  case lookup v cons of
    Just _ -> True
    Nothing -> consDef v l
consDef v (x:l) = consDef v l
consDef v [] = False

getProg :: [Decl] -> [Decl]
getProg dls = filter pred dls
  where pred (PatternDecl _ _ _) = True
        pred _ = False

sep :: [Decl] -> [[Decl]]
sep dls = partition (\ (PatternDecl f _ _) -> f) dls

funVar :: [Decl] -> [Decl] -> [VName]
funVar env ((PatternDecl f pats p):dls) =
  let args = foldr (\ x y -> fPvar x `S.union` y ) S.empty pats
      body = fPvar p
  in [ x | x <- S.toList (body S.\\ args), not (consDef x env)] `union` (funVar env dls)
funVar env [] = []

getName ((PatternDecl f pats p):dls) = f

-- obtain an abstract graph

getGraph :: [Decl] -> [[Decl]] -> [(VName, [VName])]
getGraph env ds = [(getName defs, funVar env defs) | defs <- ds]

type Path = [VName]
type Source = VName
-- first put f1 into source, then get f1's nonself neighbours ns then analyze each ns

analyze :: VName -> [(VName, [VName])] -> State (Source, [Path]) (Maybe [VName])
analyze cur graph = 
  case lookup cur graph of
    Nothing -> error $ "can't find " ++ show cur
    Just [] -> do
      (sc, paths) <- get
      let newPaths = filter (\ (h:ts) -> h /= cur ) paths 
      put (sc, newPaths)
      return Nothing
    Just nbs -> do
      (sc, paths) <- get
      if sc `elem` nbs
        then return $ Just (nub $ concat [q | q@(h:xs) <- paths, h == cur])
        else do
        let newPaths = [helper (next, cur, h, q) | q@(h:xs) <- paths, next <- nbs]
            cy = [n | n <- nbs, q@(h:xs) <- paths, n /= cur, h == cur, n `elem` q]
        put (sc, newPaths)
        ls <- mapM (\ x -> analyze x graph) $ filter (\ a -> (a /= cur) && (not $ a `elem` cy)) nbs
        let cycles = [ path | Just path <- ls]
        if null cycles
          then do
          (sc1, path1) <- get
          let neps = filter (\ (h:ts) -> h /= cur ) path1 
          put (sc1, neps)
          return Nothing
          else  return $ Just (nub $ concat cycles)
      where helper (next, cur, h, q) =
              if (next /= cur) && (h == cur) && (not $ next `elem` q)
              then (next:q) else q

              
g = [("f1", ["f7, f2"]), ("f2", ["f3","f5", "f4"]), ("f3", ["f1"]), ("f4",["f1"]), ("f5",["f4"]), ("f7", [])]
g1 = [("f1", ["f7, f2"]), ("f2", ["f3","f5"]), ("f3", []), ("f4",["f2"]), ("f5",["f4"]), ("f7", [])]
h = runState (analyze "f2" g1) ("f1", [["f2","f1"]])



