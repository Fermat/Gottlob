
{-# LANGUAGE  ScopedTypeVariables #-}
module Main where
import Language.Parser
import Language.Syntax
import Language.ProofChecking
import Language.Monad
import Language.Preprocess
import Language.PrettyPrint
import Control.Monad.Error hiding (join)
import Text.PrettyPrint(render)
import Text.Parsec(ParseError)
import System.Console.CmdArgs
import Data.Typeable
import Control.Exception
import Control.Monad.State
import System.Environment
import System.Exit
import System.IO(withFile,hGetContents,IOMode(..),hClose,openFile)
import System.Environment
import Data.Map

main = flip catches handlers $ do
  args <- getArgs
  case args of
    [filename] -> do
      cnts <- readFile filename;
      case parseModule filename cnts of
             Left e -> throw e
             Right a -> do putStrLn $ "Parsing success! \n"
--                           print $ disp a
                           putStrLn $ "Preprocessing.. \n"
                           b <- checkDefs a
                           case b of
                             Left e1 -> throw e1
                             Right (env, e) ->  do
                               putStrLn "ProofChecking success!"
                               print $ disp env
-- look at local variable                              print $ disp e


    _ -> putStrLn "usage: gottlob <filename>"
  where handlers = [Handler parseHandler, Handler typeHandler]
        typeHandler e@(ErrMsg _) = print (disp e) >> exitFailure
        parseHandler (e :: ParseError)= print (disp e) >> exitFailure

