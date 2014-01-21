
module Language.Syntax where
import qualified Data.Set as S
import Control.Monad.Reader
import Data.List
import Control.Monad.State.Lazy

type VName = String

-- extensional type, type have interpretation as set in ZF.
data EType = Ind
           | Form
           | To EType EType
           deriving (Show, Eq)

-- meta term, represent Church's simple type theory,
-- the only difference here is we don't have simple type
-- for lambda calculus, so we have \x.x : ind, not ind -> ind

data Meta = MVar VName EType
          | Forall VName EType Meta
          | Imply Meta Meta
          | Iota VName EType Meta
          | In Meta Meta
          deriving (Show)

-- nameless meta term
data MNameless = MV Int
             | FA MNameless
             | IN MNameless MNameless
             | IMP MNameless MNameless
             | IA MNameless
             deriving (Show, Eq)

data Proof = Assume VName Meta
           | PrVar VName
           | MP Proof Proof Meta
           | Inst Proof Meta Meta
           | UG VName EType Proof Meta
           | Cmp Proof Meta
           | InvCmp Proof Meta
           | Beta Proof Meta
           | InvBeta Proof Meta
           | Discharge VName Proof Meta
           deriving (Show)

type ProofScripts = [(VName, Proof, Meta)]

data Prog = Name VName 
          | Applica Prog Prog
          | Abs [VName] Prog
          | Match VName [(VName, [VName], Prog)]
          deriving Show

-- formal type for program

data Mix = FT FType
         | TM Meta -- for terms that appears in FTypes
         deriving (Show, Eq)
                  
data FType = FVar VName EType
           | Base VName [(Mix, EType)]
           | Arrow FType FType
           | Pi VName FType FType
           deriving (Show, Eq)
                    
data Datatype =
  Data VName [(VName, EType)] [(VName,FType)]    
  deriving (Show)

data Module = Module VName [Decl] deriving (Show)

data Decl = ProgDecl VName Prog
          | ProofDecl VName ProofScripts Meta
          | DataDecl Datatype
          | OperatorDecl String Int String
          deriving Show

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




              
