module Language.Syntax where
import qualified Data.Set as S
import Control.Monad.Reader
import Data.List
import Control.Monad.State.Lazy
import Data.Char
import Text.Parsec.Pos

type VName = String

-- extensional type, type have interpretation as set in ZF.
data EType = Ind
           | Form
           | EVar VName
           | To EType EType
           deriving (Show, Eq)

vars :: EType -> S.Set VName
vars (EVar x) = S.insert x S.empty
vars Ind = S.empty
vars Form = S.empty
vars (To t1 t2) = S.union (vars t1) (vars t2)

sub :: EType -> VName -> EType -> EType
sub a x Ind = Ind
sub a x Form = Form
sub a x (EVar y) = if x == y then a else EVar y
sub a x (To t1 t2) = To (sub a x t1) (sub a x t2)

data PreTerm = PVar VName             
          | Forall VName PreTerm  -- forall x.F
          | Imply PreTerm PreTerm -- F1 -> F2
          | Iota VName PreTerm -- iota x.F
          | In PreTerm PreTerm -- t :: S
          | SApp PreTerm PreTerm -- Vec U
          | TApp PreTerm PreTerm -- (Vec U) n
          | App PreTerm PreTerm -- t n
          | Lambda VName PreTerm -- \ x. t
          | Pos SourcePos PreTerm  
          deriving (Show)

isTerm :: PreTerm -> Bool
isTerm (PVar x) = isLower $ head x
isTerm (App t1 t2) = isTerm t1 && isTerm t2
isTerm (Lambda x t) = isTerm t
isTerm (Pos _ t) = isTerm t
isTerm _ = False

-- nameless meta term
data PNameless = PV Int
             | FA PNameless
             | IMP PNameless PNameless
             | IA PNameless
             | IN PNameless PNameless
             | SAP PNameless PNameless
             | TAP PNameless PNameless
             | AP PNameless PNameless
             | LM PNameless
             deriving (Show, Eq)

data Proof = Assume VName
           | PrVar VName
           | MP Proof Proof 
           | Inst Proof PreTerm 
           | UG VName Proof 
           | Cmp Proof 
           | InvCmp Proof PreTerm
           | Beta Proof 
           | InvBeta Proof PreTerm 
           | Discharge VName Proof
           | PPos SourcePos Proof
           deriving (Show)

type ProofScripts = [(VName, Proof, PreTerm)]

data Prog = Name VName 
          | Applica Prog Prog
          | Abs [VName] Prog
          | Match Prog [(VName, [VName], Prog)]
          | ProgPos SourcePos Prog
          deriving (Show, Eq)

-- formal type for program
data Args = ArgType FType
          | ArgProg Prog
          deriving (Show, Eq)
                   
data FType = FVar VName 
           | FCons VName [Args]
           | Arrow FType FType
           | Pi VName FType FType
           | FTPos SourcePos FType
           deriving (Show, Eq)

data Datatype =
  Data VName [VName] [(VName,FType)]    
  deriving (Show)

data Module = Module VName [Decl] deriving (Show)

data Decl = ProgDecl VName Prog
          | ProofDecl VName ProofScripts PreTerm
          | DataDecl Datatype
          | SetDecl VName PreTerm
          | FormOperatorDecl String Int String
          | ProgOperatorDecl String Int String
          | SpecialOperatorDecl String Int String
          deriving Show


fv :: PreTerm -> S.Set VName
fv (PVar x) = S.insert x S.empty
fv (Imply f1 f2) = fv f1 `S.union` fv f2
fv (Forall x f) = S.delete x (fv f)
fv (In t s) = fv t `S.union` (fv s)
fv (Iota x s) = S.delete x (fv s)
fv (Lambda x s) = S.delete x (fv s)
fv (App f1 f2) = fv f1 `S.union` fv f2
fv (SApp f1 f2) = fv f1 `S.union` fv f2
fv (TApp f1 f2) = fv f1 `S.union` fv f2
fv (Pos _ p) = fv p

-- get the free set variables
fVar :: PreTerm -> S.Set VName
fVar (PVar x) = S.insert x S.empty
fVar (Imply f1 f2) = fVar f1 `S.union` fVar f2
fVar (Forall x f) = S.delete x (fVar f)
fVar (In t s) = fVar s
fVar (Iota x s) = S.delete x (fVar s)
fVar (Lambda x s) = S.empty
fVar (App f1 f2) = S.empty
fVar (SApp f1 f2) = fVar f1 `S.union` fVar f2
fVar (TApp f1 f2) = fVar f1
fVar (Pos _ f) = fVar f 

type GVar a = State Int a

type BindCxt a = Reader [(VName, Int)] a

plus1 = Data.List.map (\x ->(fst x,snd x + 1))

debruijn :: PreTerm -> BindCxt PNameless
debruijn (PVar x) = do 
  Just n <- asks (lookup x) 
  return $ PV n

debruijn (Forall x f) = do 
  a <- local (((x,0):) . plus1) $ debruijn f 
  return $ FA a

debruijn (Imply f1 f2) = do
  a1 <- debruijn f1
  a2 <- debruijn f2
  return $ IMP a1 a2

debruijn (In b1 b2) = do
  a <- debruijn b1
  a1 <- debruijn b2
  return $ IN a a1

debruijn (SApp b1 b2) = do
  a <- debruijn b1
  a1 <- debruijn b2
  return $ SAP a a1

debruijn (TApp b1 b2) = do
  a <- debruijn b1
  a1 <- debruijn b2
  return $ TAP a a1

debruijn (App b1 b2) = do
  a <- debruijn b1
  a1 <- debruijn b2
  return $ AP a a1

debruijn (Iota x f) = do
  a <- local (((x,0):) . plus1) $ debruijn f 
  return $ IA a

debruijn (Lambda x f) = do
  a <- local (((x,0):) . plus1) $ debruijn f 
  return $ LM a

debruijn (Pos _ f) = debruijn f

alphaEq :: PreTerm -> PreTerm -> Bool
alphaEq t1 t2 =
  if fv t1 == fv t2
  then
    let t1' = S.foldl' (\t x -> Forall x t) t1 (fv t1)
        t2' = S.foldl' (\t x -> Forall x t) t2 (fv t1) in
    runReader (debruijn t1') [] == runReader (debruijn t2') []
  else False

instance Eq PreTerm where
  (Pos _ t1) == t2 = t1 `alphaEq` t2
  t1 == (Pos _ t2) = t1 `alphaEq` t2
  t1 == t2 = t1 `alphaEq` t2
--testform = Lambda "y" (PVar "y") == Lambda "x" (PVar "nat")


-- [M/X]M
subst :: PreTerm -> PreTerm -> PreTerm -> GVar PreTerm
subst s (PVar x) (PVar y) =
  if x == y
  then return s else return $ PVar y
                               
subst s (PVar x) (Imply f1 f2) = do
  c1 <- subst s (PVar x) f1
  c2 <- subst s (PVar x) f2
  return $ Imply c1 c2

subst s (PVar x) (TApp f1 f2) = do
  c1 <- subst s (PVar x) f1
  c2 <- subst s (PVar x) f2
  return $ TApp c1 c2

subst s (PVar x) (SApp f1 f2) = do
  c1 <- subst s (PVar x) f1
  c2 <- subst s (PVar x) f2
  return $ SApp c1 c2

subst s (PVar x) (App f1 f2) = do
  c1 <- subst s (PVar x) f1
  c2 <- subst s (PVar x) f2
  return $ App c1 c2

subst s (PVar x) (In t1 bin) =  do
  b <- subst s (PVar x) t1
  c <- subst s (PVar x) bin
  return $ In b c

subst s (PVar x) (Forall a f) =
  if x == a 
  then return $ Forall a f
  else
    if not (x `S.member` fv f) || not (a `S.member` fv s)
    then do
      c <- subst s (PVar x) f
      return $ Forall a c
    else
      do
        n <- get
        modify (+1)
        c1 <- subst (PVar (a++ show n)) (PVar a) f
        c2 <- subst s (PVar x) c1
        return $ Forall (a++ show n) c2

subst s (PVar x) (Iota a f) =
  if x == a then return $ Iota a f
  else if not (x `S.member` fv f) || not (a `S.member` fv s)
       then do
         c <- subst s (PVar x) f
         return $ Iota a c
       else
         do
           n <- get
           modify (+1)
           c1 <- subst (PVar (a++ show n)) (PVar a) f
           c2 <- subst s (PVar x) c1
           return $ Iota (a++ show n) c2

subst s (PVar x) (Lambda a f) =
  if x == a then return $ Lambda a f
  else if not (x `S.member` fv f) || not (a `S.member` fv s)
       then do
         c <- subst s (PVar x) f
         return $ Lambda a c
       else
         do
           n <- get
           modify (+1)
           c1 <- subst (PVar (a++ show n)) (PVar a) f
           c2 <- subst s (PVar x) c1
           return $ Lambda (a++ show n) c2

subst s (PVar x) (Pos _ f) = subst s (PVar x) f


              
