module Language.DependencyAnalysis where
import Language.Syntax
import Language.Pattern(partition)
import Language.PrettyPrint
--import Language.FTypeInference
import Data.List hiding(partition)



def :: VName -> [Decl] -> Bool
def v ((DataDecl pos (Data name params cons) b):l) =
  if v == name then True else def v l
def v (x:l) = def v l
def v [] = False

getProg :: [Decl] -> [Decl]
getProg dls = filter pred dls
  where pred (PatternDecl _ _ _) = True
        pred _ = False

sep :: [Decl] -> [[Decl]]
sep dls = partition (\ (PatternDecl f _ _) -> f) dls

funVar :: [Decl] -> [VName]
funVar dls = [  | (PatternDecl f pats p) <- dls, ]


