module Language.DependencyAnalysis (sep, produceDefs)where
import Language.Syntax
import Language.PrettyPrint
import Data.List hiding(partition)
import qualified Data.Set as S
import qualified Data.Map as M
import Control.Monad.State
import Debug.Trace

produceDefs :: [Decl] -> [[Decl]]
produceDefs env =
  let progs = sep $ getProg env
      g = getGraph env progs -- generate original code graph
      inter = depAnalyze g -- dep analysis
      la = label inter     -- labeling
      ga = groupGraph la g -- create label graph
      s = runTopSort ga    -- topsort
      n = toPath s la      -- convert back to paths
      res = reOrganize progs n
      in res

toPath :: [VName] -> [(VName, [VName])] -> [[VName]]
toPath s la = [ path | g' <- s, (g, path) <- la, g' == g ]
-- findPaths :: VName -> VName -> [(VName, [VName])] -> []
graph1 = [("f1", ["f2","f4", "f3"]), ("f2", ["f4"]), ("f3", ["f4", "f5"]), ("f4", ["f6"]),
          ("f11", ["f5"]), ("f5", ["f7"]), ("f12", ["f6"]), ("f6", ["f8", "f7"]), ("f8", []),
          ("f7", [])]
initials = [("f1", Nothing),("f2", Nothing),("f3", Nothing), ("f4", Nothing), ("f5", Nothing),
            ("f6", Nothing), ("f7", Nothing), ("f8", Nothing), ("f11", Nothing),("f12", Nothing)]
           
testSort = runState (topSort graph1) (initials, []) 

runTopSort :: [(VName, [VName])] -> [VName]
runTopSort g =
  let i = map (\ (x, _) -> (x, Nothing)) g in
  reverse $ (snd . snd) $runState (topSort g) (i, []) 

type Mark = Maybe Bool
-- an implementation of topological sort
topSort :: [(VName, [VName])] -> State ([(VName, Mark)], [VName]) ()
topSort graph = do
  (st, _) <- get
  let unmarks = filter (\ (x, y) -> y == Nothing) st
  if null unmarks
    then return ()
    else do
    visit graph (fst $ head unmarks)
    topSort graph

visit :: [(VName, [VName])] -> VName -> State ([(VName, Mark)], [VName]) ()
visit graph n = do
  (st, l1) <- get
  case lookup n st of
    Nothing -> error $ "can't find" ++ show n
    Just (Nothing) -> do
      let res = delete (n, Nothing) st 
          new = (n, Just False):res
          (Just ns) = lookup n graph
      put (new, l1)
      sequence [visit graph m  | m <- ns]
      (st', l) <- get
      let res' = delete (n, Just False) st'
          new' = (n, Just True):res'
      put (new', n:l)
      return ()
    Just (Just b) -> if b then return ()
                     else error "loop"

groupGraph :: [(VName, [VName])] -> [(VName, [VName])] -> [(VName, [VName])]
groupGraph la igraph =
    [ (g, helper ns la) | (g, gs) <- la, let ns = getNs igraph gs]
  where helper ns la = [ g | (g, gs) <- la, not $ null $ intersect ns gs]

getNs :: [(VName, [VName])] -> [VName] -> [VName]
getNs graph names =
 let l = nub $ concat [ ns | n <- names, let (Just ns) = lookup n graph ]
 in l \\ names


label ::[[VName]] -> [(VName, [VName])]
label paths =
  let ls = zipWith (\ a b -> a ++ show b) (repeat "G") [1..] in
  zip ls paths


-- reordering the result paths based on dependency
-- reOrder :: [(VName, [VName])] -> [[VName]] -> [[VName]]
-- reOrder g paths = 

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

-- take in an initial graph return list of paths.
depAnalyze :: [(VName, [VName])] -> [[VName]]
depAnalyze graph =
  let ls = map fst graph in
  collapse $ snd $ runState (initial ls graph) []      

-- Learn this from Google interview...
reOrganize :: [[Decl]] -> [[VName]] -> [[Decl]]
reOrganize defs st =
  [(concat [ find f defs | f <- l]) | l <- st ]
  where find f defs = concat [ q | q@((PatternDecl g pats p):res) <- defs, f == g]

type Path = [VName]
type Source = VName

collapse :: [[VName]] -> [[VName]]
collapse [] = []
collapse (a:as) =
  let newRes = [ helper a b | b <- as] in
  if newRes == as then
    a:(collapse as)
  else collapse newRes
  where helper a b = if  null $ intersect a b then b else union a b

initial :: [VName] -> [(VName, [VName])] -> State [[VName]] ()
initial [] graph = return ()
initial (a:as) graph = 
  case lookup a graph of
    Nothing -> error $ "can't find " ++ show a ++ show graph
    Just [] -> do
      modify (\ s -> [a]:s)
      initial as graph
    Just nbs -> do
      let nodes = filter (\ b -> b /= a ) nbs
          initPath = [ n:[a] | n <- nbs, n /= a] 
          maybeCyc = map (\ b -> fst $ runState (analyze b graph) (a, initPath)) nodes
          res = [ path | Just path <- maybeCyc] in
        if null res
        then do
          modify (\ s -> [a]:s)
          initial as graph
        else do
          let cys = concat res
          modify (\ s -> cys:s)
          initial (as \\ cys) graph
      
          
-- first put f1 into source, then get f1's nonself neighbours ns then analyze each ns

analyze :: VName -> [(VName, [VName])] -> State (Source, [Path]) (Maybe [VName])
analyze cur graph = 
  case lookup cur graph of
    Nothing -> error $ "can't find analyze" ++ show cur ++ show graph
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

              
-- g = [("f1", ["f7", "f2"]), ("f2", ["f3","f5", "f4"]), ("f3", ["f1"]), ("f4",["f1"]), ("f5",["f4"]), ("f7", [])]
-- g1 = [("f1", ["f7", "f2"]), ("f2", ["f3","f5"]), ("f3", []), ("f4",["f2"]), ("f5",["f4"]), ("f7", [])]
-- g2 = [("f1", []), ("f2", []), ("f3", []), ("f4",[]), ("f5",[]), ("f7", [])]
-- h = runState (analyze "f2" g1) ("f1", [["f2","f1"]])
-- h2 =  collapse $ snd $ runState (initial ["f7", "f5", "f4", "f3", "f2", "f1"] g) []


