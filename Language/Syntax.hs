
module Language.Syntax where
import qualified Data.Set as S
import Control.Monad.Reader
import Data.List
import Control.Monad.State.Lazy
import Data.Char
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
          deriving (Show)

isTerm :: PreTerm -> Bool
isTerm (PVar x) = isLower $ head x
isTerm (App t1 t2) = isTerm t1 && isTerm t2
isTerm (Lambda x t) = isTerm t
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
           | InvCmp Proof 
           | Beta Proof 
           | InvBeta Proof 
           | Discharge VName Proof 
           deriving (Show)

type ProofScripts = [(VName, Proof, PreTerm)]

data Prog = Name VName 
          | Applica Prog Prog
          | Abs [VName] Prog
          | Match Prog [(VName, [VName], Prog)]
          deriving (Show, Eq)

-- formal type for program
data Args = ArgType FType
          | ArgProg Prog
          deriving (Show, Eq)
                   
data FType = FVar VName 
           | FCons VName [Args]
           | Arrow FType FType
           | Pi VName FType FType
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

{-
fv :: Meta -> S.Set VName
fv (MVar x _) = S.insert x S.empty
fv (Imply f1 f2) = fv f1 `S.union` fv f2
fv (Forall x _ f) = S.delete x (fv f)
fv (In t s) = fv t `S.union` (fv s)
fv (Iota x _ s) = S.delete x (fv s)

type GVar a = State Int a

type BindCxt a = Reader [(VName, Int)] a

plus1 = Data.List.map (\x ->(fst x,snd x + 1))

debruijn :: Meta -> BindCxt MNameless
debruijn (MVar x _) = do 
  Just n <- asks (lookup x) 
  return $ MV n

debruijn (Forall x t f) = do 
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

debruijn (Iota x t f) = do
  a <- local (((x,0):) . plus1) $ debruijn f 
  return $ IA a

alphaMeta :: Meta -> Meta -> Bool
alphaMeta t1 t2 =
  if fv t1 == fv t2
  then
    let t1' = S.foldl' (\t x -> Forall x Ind t) t1 (fv t1)
        t2' = S.foldl' (\t x -> Forall x Ind t) t2 (fv t1) in
    runReader (debruijn t1') [] == runReader (debruijn t2') []
  else False

instance Eq Meta where
  t1 == t2 = t1 `alphaMeta` t2

--testform = In (MVar "y" Ind) (MVar "nat" (To Ind Form)) == In (MVar "x" Ind) (MVar "nat" (To Ind Form))

-- [M/X]M
subst :: Meta -> Meta -> Meta -> GVar Meta
subst s (MVar x _) (MVar y t) =
  if x == y
  then return s else return $ MVar y t
                               
subst s (MVar x u) (Imply f1 f2) = do
  c1 <- subst s (MVar x u) f1
  c2 <- subst s (MVar x u) f2
  return $ Imply c1 c2

subst s (MVar x u) (In t1 bin) =  do
  b <- subst s (MVar x u) t1
  c <- subst s (MVar x u) bin
  return $ In b c

subst s (MVar x u) (Forall a t1 f) =
  if x == a 
  then return $ Forall a t1 f
  else
    if not (x `S.member` fv f) || not (a `S.member` fv s)
    then do
      c <- subst s (MVar x u) f
      return $ Forall a t1 c
    else
      do
        n <- get
        modify (+1)
        c1 <- subst (MVar (a++ show n) u) (MVar a u) f
        c2 <- subst s (MVar x u) c1
        return $ Forall (a++ show n) t1 c2

subst s (MVar x u) (Iota a t1 f) =
  if x == a then return $ Iota a t1 f
  else if not (x `S.member` fv f) || not (a `S.member` fv s)
       then do
         c <- subst s (MVar x u) f
         return $ Iota a t1 c
       else
         do
           n <- get
           modify (+1)
           c1 <- subst (MVar (a++ show n) u) (MVar a u) f
           c2 <- subst s (MVar x u) c1
           return $ Iota (a++ show n) t1 c2

-}


              
