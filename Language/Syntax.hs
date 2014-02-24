module Language.Syntax
       (VName, EType(..), vars, sub,
        PreTerm(..), Proof(..), ProofScripts,
        Prog(..), Args(..), FType(..),
        Datatype(..), Module(..), Decl(..),
        fv, fVar, fPrVar, runSubst, runSubPre, runSubProof, naiveSub) where

import Control.Monad.State.Lazy
import Control.Monad.Reader

import Data.Char
import qualified Data.Set as S
import Data.List

import Text.Parsec.Pos

type VName = String

-- extensional type, type have interpretation as set in ZF.
data EType = Ind
           | Form
           | EVar VName
           | To EType EType
           deriving (Show, Eq)

vars :: EType -> S.Set VName
vars (To t1 t2) = S.union (vars t1) (vars t2)
vars (EVar x) = S.insert x S.empty
vars _ = S.empty

sub :: EType -> VName -> EType -> EType
sub a x (To t1 t2) = To (sub a x t1) (sub a x t2)
sub a x (EVar y) = if x == y then a else EVar y
sub a x d = d

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
           | Discharge VName (Maybe PreTerm) Proof
           | PLam VName Proof
           | PApp Proof Proof
           | PFApp Proof PreTerm
           | PPos SourcePos Proof
           deriving (Show, Eq)

-- get all the free vars
fPrVar :: Proof -> S.Set VName
fPrVar (PPos a p) = fPrVar p
fPrVar (Assume x) = S.empty
fPrVar (PrVar x) = S.insert x S.empty
fPrVar (MP p1 p2) = fPrVar p1 `S.union` fPrVar p2
fPrVar (PApp p1 p2) = fPrVar p1 `S.union` fPrVar p2
fPrVar (Inst p1 t) = fPrVar p1 `S.union` fv t
fPrVar (UG a p) = S.delete a (fPrVar p)
fPrVar (PLam a p) = S.delete a (fPrVar p)
fPrVar (Discharge a t p) =
  case t of
    Nothing -> S.delete a (fPrVar p)
    Just b -> S.delete a (fPrVar p) `S.union` fv b
fPrVar (Cmp p) = fPrVar p
fPrVar (Beta p) = fPrVar p
fPrVar (InvCmp p1 t) = fPrVar p1 `S.union` fv t
fPrVar (InvBeta p1 t) = fPrVar p1 `S.union` fv t
fPrVar (PFApp p1 t) = fPrVar p1 `S.union` fv t
-- naive sub proof 
naiveSub :: Proof -> Proof -> Proof -> Proof
naiveSub p (PrVar x) (PrVar y) =
  if x == y then p else PrVar y
                               
naiveSub p (PrVar x) (MP p1 p2) = 
  let a1 = naiveSub p (PrVar x) p1
      a2 = naiveSub p (PrVar x) p2 in
  MP a1 a2
  
naiveSub p (PrVar x) (Inst p1 t) =
  let a = naiveSub p (PrVar x) p1 in
  Inst a t
  
naiveSub p (PrVar x) (UG y p1) = UG y (naiveSub p (PrVar x) p1)
                                     
naiveSub p (PrVar x) (Cmp p1) = Cmp (naiveSub p (PrVar x) p1)
                                     
naiveSub p (PrVar x) (InvCmp p1 t) =
  InvCmp (naiveSub p (PrVar x) p1) t

naiveSub p (PrVar x) (Beta p1) =
  Beta (naiveSub p (PrVar x) p1)
                                    
naiveSub p (PrVar x) (InvBeta p1 t) =
  InvBeta ( naiveSub p (PrVar x) p1) t

naiveSub p (PrVar x) (Discharge y t p1) = Discharge y t (naiveSub p (PrVar x) p1)
  
naiveSub p (PrVar x) (PLam y p1) =  PLam y (naiveSub p (PrVar x) p1)
  
naiveSub p (PrVar x) (PApp p1 p2) = 
  let a1 = naiveSub p (PrVar x) p1
      a2 = naiveSub p (PrVar x) p2 in
  PApp a1 a2
  
naiveSub p (PrVar x) (PFApp p1 t) = 
  PFApp (naiveSub p (PrVar x) p1) t
  
naiveSub p (PrVar x) (PPos a p1) =
  PPos a (naiveSub p (PrVar x) p1)

-- capture avoiding subst for proof
runSubProof :: Proof -> Proof -> Proof -> Proof
runSubProof t x t1 = fst $ runState (subProof t x t1) 0

runSubPre :: PreTerm -> PreTerm -> Proof -> Proof
runSubPre t x t1 = fst $ runState (subPre t x t1) 0

subProof :: Proof -> Proof -> Proof -> GVar Proof
subProof p (PrVar x) (PrVar y) =
  if x == y then return p else return $ PrVar y
                               
subProof p (PrVar x) (MP p1 p2) = do
  a1 <- subProof p (PrVar x) p1
  a2 <- subProof p (PrVar x) p2
  return $ MP a1 a2
  
subProof p (PrVar x) (Inst p1 t) =
  subProof p (PrVar x) p1 >>= \ a -> return $ Inst a t
  
subProof p (PrVar x) (UG y p1) =
  if x == y || not (x `S.member` fPrVar p1) then return $ UG y p1
  else if not (y `S.member` fPrVar p)
       then do
         c <- subProof p (PrVar x) p1
         return $ UG y c
       else do
         n <- get
         modify (+1)
         c1 <- subPre (PVar (y++ show n)) (PVar y) p1
         c2 <- subProof p (PrVar x) c1
         return $ UG (y++ show n) c2
                                     
subProof p (PrVar x) (Cmp p1) =
  subProof p (PrVar x) p1 >>= \ a -> return $ Cmp a
                                     
subProof p (PrVar x) (InvCmp p1 t) =
  subProof p (PrVar x) p1 >>= \ a -> return $ InvCmp a t

subProof p (PrVar x) (Beta p1) =
  subProof p (PrVar x) p1 >>= \a -> return $ Beta a
                                    
subProof p (PrVar x) (InvBeta p1 t) =
  subProof p (PrVar x) p1 >>= \ a -> return $ InvBeta a t

subProof p (PrVar x) (Discharge y t p1) = 
  if x == y || not (x `S.member` fPrVar p1) then return $ Discharge y t p1
  else if not (y `S.member` fPrVar p)
       then do
         c <- subProof p (PrVar x) p1
         return $ Discharge y t c
       else do
         n <- get
         modify (+1)
         c1 <- subProof (PrVar (y++ show n)) (PrVar y) p1
         c2 <- subProof p (PrVar x) c1
         return $ Discharge (y++ show n) t c2

subProof p (PrVar x) (PLam y p1) =
  if x == y || not (x `S.member` fPrVar p1) then return $ PLam y p1
  else if not (y `S.member` fPrVar p)
       then do
         c <- subProof p (PrVar x) p1
         return $ PLam y c
       else do
         n <- get
         modify (+1)
         c1 <- subProof (PrVar (y++ show n)) (PrVar y) p1
         c2 <- subProof p (PrVar x) c1
         return $ PLam (y++ show n) c2

subProof p (PrVar x) (PApp p1 p2) = do
  a1 <- subProof p (PrVar x) p1
  a2 <- subProof p (PrVar x) p2
  return $ PApp a1 a2
  
subProof p (PrVar x) (PFApp p1 t) = 
  subProof p (PrVar x) p1 >>= \ a -> return $ PFApp a t
  
subProof p (PrVar x) (PPos a p1) =
  subProof p (PrVar x) p1 >>= \ b -> return $ PPos a b

subPre :: PreTerm -> PreTerm -> Proof -> GVar Proof
subPre p (PVar x) (PrVar y) = return $ PrVar y
subPre p (PVar x) (MP p1 p2) = do
  a1 <- subPre p (PVar x) p1
  a2 <- subPre p (PVar x) p2
  return $ MP a1 a2
  
subPre p (PVar x) (Inst p1 t) = do
  a1 <- subPre p (PVar x) p1
  t1 <- subst p (PVar x) t
  return $ Inst a1 t1
  
subPre p (PVar x) (UG y p1) =
  if x == y || not (x `S.member` fPrVar p1) then return $ UG y p1
  else if not (y `S.member` fv p)
       then do
         c <- subPre p (PVar x) p1
         return $ UG y c
       else do
         n <- get
         modify (+1)
         c1 <- subPre (PVar (y++ show n)) (PVar y) p1
         c2 <- subPre p (PVar x) c1
         return $ UG (y++ show n) c2

subPre p (PVar x) (PLam y p1) =
  if x == y || not (x `S.member` fPrVar p1) then return $ PLam y p1
  else if not (y `S.member` fv p)
       then do
         c <- subPre p (PVar x) p1
         return $ PLam y c
       else do
         n <- get
         modify (+1)
         c1 <- subProof (PrVar (y++ show n)) (PrVar y) p1
         c2 <- subPre p (PVar x) c1
         return $ PLam (y++ show n) c2

subPre p (PVar x) (Discharge y Nothing p1) = 
  if x == y || not (x `S.member` fPrVar p1) then return $ Discharge y Nothing p1
  else if not (y `S.member` fv p)
       then do
         c <- subPre p (PVar x) p1
         return $ Discharge y Nothing c
       else do
         n <- get
         modify (+1)
         c1 <- subProof (PrVar (y++ show n)) (PrVar y) p1
         c2 <- subPre p (PVar x) c1
         return $ Discharge (y++ show n) Nothing c2

subPre p (PVar x) (Discharge y (Just t) p1) = 
  subst p (PVar x) t >>= \ t1 ->
  if x == y || not (x `S.member` fPrVar p1) then return $ Discharge y (Just t1) p1
  else if not (y `S.member` fv p)
       then do
         c <- subPre p (PVar x) p1
         return $ Discharge y (Just t1) c
       else do
         n <- get
         modify (+1)
         c1 <- subProof (PrVar (y++ show n)) (PrVar y) p1
         c2 <- subPre p (PVar x) c1
         return $ Discharge (y++ show n) (Just t1) c2
  
subPre p (PVar x) (Cmp p1) = 
  subPre p (PVar x) p1 >>= \ a -> return $ Cmp a

subPre p (PVar x) (InvCmp p1 t) = do
  a1 <- subPre p (PVar x) p1
  t1 <- subst p (PVar x) t
  return $ InvCmp a1 t1
  
subPre p (PVar x) (Beta p1) = subPre p (PVar x) p1 >>= \ a -> return $ Beta a
subPre p (PVar x) (InvBeta p1 t) = do
  a <- subPre p (PVar x) p1
  t1 <- subst p (PVar x) t
  return $ InvBeta a t1
  
subPre p (PVar x) (PApp p1 p2) = do
  a1 <- subPre p (PVar x) p1
  a2 <- subPre p (PVar x) p2
  return $ PApp a1 a2
  
subPre p (PVar x) (PFApp p1 t) = do
  a1 <- subPre p (PVar x) p1
  t1 <- subst p (PVar x) t
  return $ PFApp a1 t1

subPre p (PVar x) (PPos a p1) = subPre p (PVar x) p1 >>= \ b -> return $ PPos a b

  
type ProofScripts = [(VName, Proof, Maybe PreTerm)]

data Prog = Name VName 
          | Applica Prog Prog
          | Abs [VName] Prog
          | Match Prog [(VName, [VName], Prog)]
          | ProgPos SourcePos Prog
            -- The way we deal with let(rec) is lift them in to global context as
            -- prog def. Because tranlating them into lambda term will be a disaster.
          | Let [(VName, Prog)] Prog
            -- p1 >>= p2, haskell style monadic operation
          | Bind Prog Prog
          deriving (Show, Eq)

-- formal type for program, e.g. Nat -> Nat
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
          | DataDecl SourcePos Datatype
          | SetDecl VName PreTerm
          | TacDecl VName [VName] (Either Proof ProofScripts)
          | FormOperatorDecl String Int String
          | ProgOperatorDecl String Int String
          deriving Show

-- get all free variables
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

plus1 = Data.List.map (\x ->(fst x,snd x + 1))

-- debruijn only deals with closed preterm. To
-- compare open preterms, we simply closed these
-- by a fold of forall binder at the top.
alphaEq :: PreTerm -> PreTerm -> Bool
alphaEq t1 t2 =
  if fv t1 == fv t2
  then
    let t1' = S.foldl' (\t x -> Forall x t) t1 (fv t1)
        t2' = S.foldl' (\t x -> Forall x t) t2 (fv t1) in
    runReader (debruijn t1') [] == runReader (debruijn t2') []
  else False
-- Since debruijn and fv all take care of position,
-- we don't need to care about that when we do the comparison
instance Eq PreTerm where
  t1 == t2 = t1 `alphaEq` t2

-- [M/X]M
runSubst :: PreTerm -> PreTerm -> PreTerm -> PreTerm
runSubst t x t1 = fst $ runState (subst t x t1) 0
  
subst :: PreTerm -> PreTerm -> PreTerm -> GVar PreTerm
subst s (PVar x) (PVar y) =
  if x == y then return s else return $ PVar y
                               
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
  if x == a || not (x `S.member` fv f) then return $ Forall a f
  else if not (a `S.member` fv s)
       then do
         c <- subst s (PVar x) f
         return $ Forall a c
       else do
         n <- get
         modify (+1)
         c1 <- subst (PVar (a++ show n)) (PVar a) f
         c2 <- subst s (PVar x) c1
         return $ Forall (a++ show n) c2

subst s (PVar x) (Iota a f) =
  if x == a || not (x `S.member` fv f) then return $ Iota a f
  else if not (a `S.member` fv s)
       then do
         c <- subst s (PVar x) f
         return $ Iota a c
       else do
         n <- get
         modify (+1)
         c1 <- subst (PVar (a++ show n)) (PVar a) f
         c2 <- subst s (PVar x) c1
         return $ Iota (a++ show n) c2

subst s (PVar x) (Lambda a f) =
  if x == a || not (x `S.member` fv f) then return $ Lambda a f
  else if not (a `S.member` fv s)
       then do
         c <- subst s (PVar x) f
         return $ Lambda a c
       else do
         n <- get
         modify (+1)
         c1 <- subst (PVar (a++ show n)) (PVar a) f
         c2 <- subst s (PVar x) c1
         return $ Lambda (a++ show n) c2

subst s (PVar x) (Pos _ f) = subst s (PVar x) f


              
