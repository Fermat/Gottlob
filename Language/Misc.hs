module Language.Misc where
import Language.ProofChecking
import Language.Program
import Language.Syntax
import Language.Monad
import Control.Monad.State
import Control.Monad.Error
import Control.Monad.Reader
import Text.Parsec
import Text.Parsec.Language
import Text.Parsec.Pos
import Text.Parsec.Indent
import Text.Parsec.Token


f = \ y -> let x = y in y
g = \ y -> let x = y in y

data Tree a = Leaf
            | Node (Tree a) a (Tree a)
            deriving(Show, Eq)

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
