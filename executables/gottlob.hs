module Main where
import Language.Parser
import Language.Syntax
-- import Language.ProofChecking
import Language.Monad
import Language.Preprocess
import Language.PrettyPrint
import Control.Monad.Error hiding (join)
import Text.PrettyPrint(render)
import System.Console.CmdArgs
import Data.Typeable
import Control.Exception
import Control.Monad.State
import System.Environment
import System.Exit
import System.IO(withFile,hGetContents,IOMode(..),hClose,openFile)
import System.Environment
import Data.Map

main = do
  args <- getArgs
  case args of
    [filename] -> do
      cnts <- readFile filename;
      case parseModule filename cnts of
             Left e -> putStrLn $ show e
             Right a -> do putStrLn $ "Parsing success! \n"
                           print $ disp a
                           putStrLn $ "Preprocessing.. \n"
                           b <- checkDefs a
                           case b of
                             Left e1 -> putStrLn $ show e1
                             Right (env, e) -> do
                               putStrLn "ProofChecking success!"
                               putStrLn $ show env ++ ":prf:"++ show e
                           -- unknow <- runErrorT (runFreshMT (runStateT (typechecker a) (Data.Map.empty,Data.Map.empty)))
                           -- case unknow of
                           --   Left e -> do
                           --     putStrLn $ show (disp e)
                           --   Right (s,env) -> do
                           --     putStrLn $ show (disp s) ++ "\n"
                           --     putStrLn $ show (disp (fst env)) ++ "\n"
                           --     putStrLn $ show (disp (snd env))

    _ -> putStrLn "usage: gottlob <filename>"

