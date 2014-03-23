{-# LANGUAGE BangPatterns, NoMonomorphismRestriction, GADTs, RankNTypes #-}
module Language.Misc where
-- import Language.ProofChecking
-- import Language.Program
-- import Language.Syntax
-- import Language.Monad
import Control.Monad.State
import Control.Monad.Error
import Control.Monad.Reader
import Text.Parsec
import Text.Parsec.Language
import Text.Parsec.Pos
import Text.Parsec.Indent
import Text.Parsec.Token
import Data.List
import Data.Function(on)


-- data Observer a b where
--   OHead :: (a -> b) -> Observer a b
--   OTail :: Observer a b -> Observer a b

-- hd s = s (OHead (\ x -> x))

-- tl s = \ o -> s (OTail o)

-- sPlus :: (Observer a b -> c) -> (Observer a b -> c) -> Observer a b -> (Observer a b -> c)
-- sPlus s1 s2 (OHead f) = f (hd s1 + tl s2)
-- sPlus s1 s2 (OTail o) = sPlus (tl s1) (tl s2) o


-- fi o = case o of  
--            OHead f -> f 0
--            OTail (OHead f) -> f 1
--            OTail (OTail o') -> sPlus (fi (OTail o')) (fi o') 



data N = Z | S N deriving (Show, Eq)
add n m = case n of
  Z -> m
  S n' -> S (add n' m)

f = \ y -> let x = y in y
g = \ y -> let x = y in y


insertion b Leaf = Node Leaf b Leaf
insertion b (Node tr1 a tr2) =
  if b < a
  then Node (insertion b tr1) a tr2
  else Node tr1 a (insertion b tr2)


deletion b Leaf = Leaf

deletion b (tr@(Node Leaf a Leaf)) | a == b = Leaf
                                   | otherwise = tr

deletion b (tr@(Node (Node ltr1 al ltr2) a Leaf))
  | a == b = Node ltr1 al ltr2
  | b < a = Node (deletion b (Node ltr1 al ltr2)) a Leaf
  | otherwise = tr

deletion b (tr@(Node Leaf a (Node ltr1 al ltr2)))
  | a == b = Node ltr1 al ltr2
  | b > a = Node Leaf a (deletion b (Node ltr1 al ltr2))
  | otherwise = tr

deletion b (Node (Node ltr1 al ltr2) a (Node rtr1 ar rtr2))
  | a == b =
    let c = getSuc b rtr1 in
    Node (Node ltr1 al ltr2) c (Node (deletion c rtr1) ar rtr2)
  | b < a = Node (deletion b (Node ltr1 al ltr2)) a (Node rtr1 ar rtr2)
  | b > a = Node (Node ltr1 al ltr2) a (deletion b (Node rtr1 ar rtr2))
  where getSuc b (Node (Node sub1 a1 sub2) a rtr) = getMin (Node sub1 a1 sub2)
        getSuc b (Node Leaf a rtr) = a
        getMin (Node Leaf a tr) = a
        getMin (Node (Node tr1 b tr2) a tr) = getMin (Node tr1 b tr2)
        getMin a = error $ "hmm" ++ show a



mittree = foldr insertion Leaf [ 7, 6, 23, 18, 13, 10, 20, 12, 3, 16, 5, 15]


-- myFib 0 (0, 1) = (0, 0)
-- myFib 1 (0, 1) = (1, 0)
-- myFib 2 (1, 0) = (1 + 0 , 1)
-- myFib 3 (1, 1) = (2, 1)
-- myFib 4 (2, 1) = (3, 2) ..



-- premature opt version. may take constant space.
fib n = go n (0,1)
  where
    go !n (!a, !b) | n==0      = a
                   | otherwise = go (n-1) (b, a+b)


-- Time & Space O(n) don't even try to do tail optimization, aka, premature optimization.
myFib 0 = (0, 0)
myFib 1 = (1, 0)
myFib n' = let (c, d) = myFib (n' - 1) in
           (c + d, c)
fibb n = fst (myFib n)

-- slow Fib exponential, Time & Space O(2^n)
sFib 0 = 0
sFib 1 = 1
sFib n = sFib (n - 1) + sFib (n - 2)

tag :: Tree a -> Int -> (Tree (Int, a), Int)
tag Leaf b = (Leaf, b)
tag (Node l i r) b =
  let a = tag l (b+1)
      b1 = fst a
      b2 = snd a
      c1 = tag r b2
      c2 = fst c1
      c3 = snd c1
  in (Node b1 (b, i) c2, c3)

tr = Node (Node (Node Leaf "r11" Leaf) "r1" Leaf) "root" (Node Leaf "r1" Leaf)


-- vecc u n = Base "Vec" [(FVar u (To Ind Form), To Ind Form), (FVar n Ind, Ind)]

-- vec = Data "Vec" [("U", To Ind Form), ("a", Ind)]
--       [("vnil", vecc "U" "0"),
--        ("vcons", Pi "n" (FVar "Nat" (To Ind Form))
--                  (Arrow (FVar "U" (To Ind Form)) (Arrow (vecc "U" "n") (vecc "U" "n+1"))))]
-- testvec = toSet vec

-- comptest1 :: IO ()
-- comptest1 = do
--       c <- runErrorT $ runStateT (runReaderT (runGlobal (repeatComp (snd testvec))) emptyEnv) emptyPrfEnv 
--       case c of
--         Left e -> putStrLn e
--         Right a -> putStrLn $ show $ fst a

-- testParse :: (SourcePos -> SourcePos) 
--           -> IndentParser String () a 
--           -> String -> Either ParseError a

-- testParse f p src = fst $ flip runState (f $ initialPos "") $ runParserT p () "" src


ks = knapsack []

knapsack :: [(Int, Int)] -> [(Int, Int)] -> Int -> [(Int, Int)]
knapsack xs [] _   = xs
knapsack xs ys max =
    foldr (maxOf) [] (xs: [knapsack (y:xs) (delete y ys) max
                           | y <- ys, weightOf(y:xs) <= max ] ) where
      weightOf = sum . map snd

maxOf :: [(Int, Int)] -> [(Int, Int)] -> [(Int, Int)]
maxOf a b = maximumBy (compare `on` valueOf) [a,b] where
            valueOf = sum . map fst
-- knapsack' ::  [(Int, Int)] -> [(Int, Int)]
inv = [("map",9,150), ("compass",13,35), ("water",153,200), ("sandwich",50,160),
       ("glucose",15,60), ("tin",68,45), ("banana",27,60), ("apple",39,40),
       ("cheese",23,30), ("beer",52,10), ("cream",11,70), ("camera",32,30),
       ("tshirt",24,15), ("trousers",48,10), ("umbrella",73,40),
       ("waterproof trousers",42,70), ("overclothes",43,75), ("notecase",22,80),
       ("sunglasses",7,20), ("towel",18,12), ("socks",4,50), ("book",30,10)]

knapsack' = foldr addItem (repeat (0,[]))
  where addItem (name,w,v) list = left ++ zipWith max right newlist
          where
            newlist = map (\(val, names)->(val + v, name:names)) list
            (left,right) = splitAt w list


fibs = 0 : 1 : zipWith (+) fibs (tail fibs)

data Tree a = Leaf
            | Node (Tree a) a (Tree a)
            deriving(Show, Eq)

-- zipp [] [] = []
-- zipp (a:t) (b:t') = zipp a b
idd = \ x -> x
exp11 = let x = idd in x
