{-# LANGUAGE NamedFieldPuns, DeriveDataTypeable, ParallelListComp  #-}
module Language.Monad where
import Language.Syntax
import Language.PrettyPrint
import Text.PrettyPrint
import Data.Typeable
import Control.Monad.State
import Control.Monad.Error
import qualified Data.Map as M
import Control.Applicative hiding (empty)
import Control.Monad.Reader
import Control.Monad.Error
import Text.Parsec.Pos
import Control.Exception(Exception)

type Global a =StateT Env (StateT PrfEnv (ErrorT PCError IO)) a
                 -- deriving (Functor, Applicative, Monad,
                 --           MonadState Env, MonadError TypeError, MonadIO)

data Env = Env{ progDef::M.Map VName PreTerm,
                setDef::M.Map VName (PreTerm, EType),
                proofCxt::M.Map VName (ProofScripts, PreTerm),
                tacticDef :: M.Map VName Proof}
         deriving Show

data PrfEnv = PrfEnv { assumption::[(VName, PreTerm)],
                       localProof :: M.Map VName (Proof, PreTerm),
                       localEType :: M.Map VName EType}
            deriving Show

emptyEnv :: Env
emptyEnv = Env {progDef = M.empty, setDef = M.empty, proofCxt=M.empty,
                tacticDef=M.empty}

emptyPrfEnv :: PrfEnv
emptyPrfEnv = PrfEnv { assumption = [], localProof=M.empty, localEType=M.empty}

newPrfEnv :: [(VName, EType)] -> PrfEnv
newPrfEnv e = PrfEnv { assumption = [], localProof=M.empty, localEType=M.fromList e}
                  
extendProgDef :: VName -> PreTerm -> Env -> Env
extendProgDef v t e@(Env {progDef}) = e{progDef = M.insert v t progDef}

extendTacticDef :: VName -> Proof -> Env -> Env
extendTacticDef v t e@(Env {tacticDef}) = e{tacticDef = M.insert v t tacticDef}

extendProofCxt :: VName -> ProofScripts -> PreTerm -> Env -> Env
extendProofCxt v ps f e@(Env {proofCxt}) = e{proofCxt = M.insert v (ps,f) proofCxt}

extendSetDef :: VName -> PreTerm -> EType -> Env -> Env
extendSetDef v t t1 e@(Env {setDef}) = e{setDef = M.insert v (t, t1) setDef}

pushAssump :: VName -> PreTerm -> PrfEnv -> PrfEnv
pushAssump v f e@(PrfEnv {assumption}) = e{assumption = (v,f):assumption}

popAssump :: PrfEnv -> PrfEnv
popAssump e@(PrfEnv {assumption}) = e{assumption = tail assumption}

extendLocalProof :: VName -> Proof -> PreTerm -> PrfEnv -> PrfEnv
extendLocalProof v p f e@(PrfEnv {localProof}) = e{localProof = M.insert v (p,f) localProof}

extendLocalEType :: VName -> EType -> PrfEnv -> PrfEnv
extendLocalEType v p e@(PrfEnv {localEType}) = e{localEType = M.insert v p localEType}

--------------

instance Disp Env where
  disp env = hang (text "Program Definitions") 2 (vcat
                [disp n <+> text "=" <+> disp t | (n, t) <- M.toList $ progDef env])  $$
             hang (text "Set/Formula Definitions") 2 (vcat
                                                      [disp n <+> text":"<+> disp t <+> text "=" <+> disp f | (n,(f,t)) <- M.toList $ setDef env]) $$
             hang (text "Proofs Context") 2 (vcat
                [ disp (ProofDecl n ps f) | (n,(ps,f)) <- M.toList $ proofCxt env]) $$
             hang (text "Tactic Definitions") 2 (vcat
                [disp n <+> text "=" <+> disp t | (n, t) <- M.toList $ tacticDef env]) 




instance Disp PrfEnv where
  disp env = hang (text "Current Local Assumptions") 2 (vcat
                [parens (disp n) <+> text ":" <+> disp t | (n, t) <- assumption env])  $$
             hang (text "Local Proofs") 2 (vcat
                                           [disp n <+> text"="<+> disp p <+> text ":" <+> disp f | (n,(p,f)) <- M.toList $ localProof env]) $$
             hang (text "Local EType Assigments") 2 (vcat
                [ disp n <+> text ":" <+> disp t | (n,t) <- M.toList $ localEType env])
----------------
-- error handling, came from Garrin's code

data PCError = ErrMsg [ErrInfo]
               deriving (Show, Typeable)

data ErrInfo = ErrInfo Doc -- A Summary
               [(Doc,Doc)] -- A list of details
             | ErrLocPre SourcePos PreTerm
             | ErrLocProof SourcePos Proof
             | ErrLocProg SourcePos Prog
             deriving (Show, Typeable)

instance Error PCError where
  strMsg s = ErrMsg [ErrInfo (text s) []]
  noMsg = strMsg "<unknown>"

instance Exception PCError

instance Disp PCError where
  disp (ErrMsg rinfo) =
       hang (pos positions) 2 (summary $$ nest 2 detailed $$  vcat terms)
    where info = reverse rinfo
          positions = [el | el <- info, f el == True]
          f (ErrLocPre _ _) = True
          f (ErrLocProof _ _) = True
          f (ErrLocProg _ _) = True
          f _ = False
          messages = [ei | ei@(ErrInfo _ _) <- info]
          details = concat [ds | ErrInfo _ ds <- info]
          pos ((ErrLocPre sp _):_) = disp sp
          pos ((ErrLocProof sp _):_) = disp sp
          pos ((ErrLocProg sp _):_) = disp sp
          pos _ = text "unknown position" <> colon
          summary = vcat [s | ErrInfo s _ <- messages]
          detailed = vcat [(int i <> colon <+> brackets label) <+> d |
                           (label,d) <- details | i <- [1..]]
          terms = [hang (text "in the expression:") 2 (dispExpr t) |  t <- take 4 positions]
          dispExpr (ErrLocProof _ p) = disp p
          dispExpr (ErrLocPre _ p) = disp p
          dispExpr (ErrLocProg _ p) = disp p

addProofErrorPos ::  SourcePos -> Proof -> PCError -> Global a
addProofErrorPos pos p (ErrMsg ps) = throwError (ErrMsg (ErrLocProof pos p:ps))

addProgErrorPos ::  SourcePos -> Prog -> PCError -> Global a
addProgErrorPos pos p (ErrMsg ps) = throwError (ErrMsg (ErrLocProg pos p:ps))

addPreErrorPos ::  SourcePos -> PreTerm -> PCError -> Global a
addPreErrorPos pos p (ErrMsg ps) = throwError (ErrMsg (ErrLocPre pos p:ps))

ensure :: Disp d => Bool -> d -> Global ()
ensure p m = unless p $ die m

die :: Disp d => d -> Global a
die msg = pcError (disp msg) []

pcError :: Disp d => d -> [(Doc, Doc)] -> Global a
pcError summary details = throwError (ErrMsg [ErrInfo (disp summary) details])

addErrorInfo :: Disp d => d -> [(Doc, Doc)] -> PCError -> PCError
addErrorInfo summary details (ErrMsg ms) = ErrMsg (ErrInfo (disp summary) details:ms)

withErrorInfo :: (Disp d) => d -> [(Doc, Doc)] -> Global a -> Global a
withErrorInfo summary details m = m `catchError` (throwError . addErrorInfo summary details)

emit :: (Show a, MonadIO m) => a -> m ()
emit m = liftIO $ print m

sameFormula :: PreTerm -> PreTerm -> Global ()
actual `sameFormula` expected =
  unless (actual == expected) $
  pcError "Couldn't match expected formula with actual formula."
  [(text "Expected Formula",disp expected), (text "Actual Formula", disp actual)]

(<++>) :: (Show t1, Show t2, Disp t1, Disp t2) => t1 -> t2 -> Doc
t1 <++> t2 = disp t1 <+> disp t2

($$$) :: (Disp d, Disp d1) => d -> d1 -> Doc
t1 $$$ t2 =  disp t1 $$ disp t2




