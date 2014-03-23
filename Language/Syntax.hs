module Language.Syntax
       (VName, EType(..), vars, sub, farity,
        PreTerm(..), ProofScripts, 
        Prog(..), Args(..), FType(..), Assumption(..),
        Datatype(..), Module(..), Decl(..), TScheme(..),
        fv,fVar, freeVar, runSubst, naiveSub, fPvar, partition) where

import Control.Monad.State.Lazy
import Control.Monad.Reader

import Data.Char
import qualified Data.Set as S
import Data.List hiding (partition)

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
            -- prog
          | App PreTerm PreTerm -- t n
          | Lambda VName PreTerm -- \ x. t
            -- proof term
          | MP PreTerm PreTerm -- mp p1 by p2
          | Inst PreTerm PreTerm -- inst p1 by p2
          | UG VName PreTerm     -- ug x . p
          | Cmp PreTerm          -- cmp p
          | SimpCmp PreTerm -- simpCmp p
          | InvSimp PreTerm PreTerm
          | InvCmp PreTerm PreTerm  -- invcmp p from F
          | Beta PreTerm            -- beta p
          | InvBeta PreTerm PreTerm  -- invbeta p from F
          | Discharge VName (Maybe PreTerm) PreTerm -- discharge a : F . p

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

-- naive sub for proof 
naiveSub :: Prog -> Prog -> Prog -> Prog
naiveSub p (Name x) (Name y) =
  if x == y then p else Name y
                               
naiveSub p (Name x) (TMP p1 p2) = 
  let a1 = naiveSub p (Name x) p1
      a2 = naiveSub p (Name x) p2 in
  TMP a1 a2
  
naiveSub p (Name x) (TInst p1 t) =
  let a = naiveSub p (Name x) p1 in
  TInst a t
  
naiveSub p (Name x) (TUG y p1) = TUG y (naiveSub p (Name x) p1)
                                     
naiveSub p (Name x) (TCmp p1) = TCmp (naiveSub p (Name x) p1)
                                     
naiveSub p (Name x) (TInvCmp p1 t) =
  TInvCmp (naiveSub p (Name x) p1) t

naiveSub p (Name x) (TSimpCmp p1) = TSimpCmp (naiveSub p (Name x) p1)
                                     
naiveSub p (Name x) (TInvSimp p1 t) =
  TInvSimp (naiveSub p (Name x) p1) t

naiveSub p (Name x) (TBeta p1) =
  TBeta (naiveSub p (Name x) p1)
                                    
naiveSub p (Name x) (TInvBeta p1 t) =
  TInvBeta ( naiveSub p (Name x) p1) t

naiveSub p (Name x) (TDischarge y t p1) = TDischarge y t (naiveSub p (Name x) p1)
  
naiveSub p (Name x) (Abs y p1) =  Abs y (naiveSub p (Name x) p1)
  
naiveSub p (Name x) (AppPre p1 p2) = 
  let a1 = naiveSub p (Name x) p1 in
      -- a2 = naiveSub p (Name x) p2 in
  AppPre a1 p2

naiveSub p (Name x) (Applica p1 p2) = 
  let a1 = naiveSub p (Name x) p1
      a2 = naiveSub p (Name x) p2 in
  Applica a1 a2

--naiveSub p (Name x) (TIota y p1) =  TI y (naiveSub p (Name x) p1)

naiveSub p (Name x) (ProgPos a p1) =
  ProgPos a (naiveSub p (Name x) p1)

naiveSub p (Name x) er = error $ show er

data Assumption = Assume VName deriving Show
--                      a = p1 : F or [a] : F
type ProofScripts = [(VName, Either Assumption Prog, Maybe Prog)]

fPvar :: Prog -> S.Set VName
fPvar (Name x) = S.insert x S.empty
fPvar (Applica p1 p2) = fPvar p1 `S.union` fPvar p2
fPvar (Abs xs p) = fPvar p S.\\ (S.fromList xs)
fPvar (Match p ls) = fPvar p `S.union` (foldr (\ x y -> helper x `S.union` y) S.empty ls)
  where helper (c, pat, p) =
          fPvar p S.\\ (foldr (\ x y -> S.union (fPvar x) y ) (S.insert c S.empty) pat)

fPvar (Let ((x,t):[]) p) = S.union (fPvar t) $ S.delete x (fPvar p)
fPvar (Let ((x,t):xs) p) = S.union (fPvar t) $ S.delete x (fPvar (Let xs p))
  -- ((fPvar p) `S.union` (helper xs)) S.\\ helper2 xs
  -- where helper xs = foldr (\ (x, t) y -> fPvar t `S.union` y ) S.empty xs
  --       helper2 xs = foldr (\ (x, t) y -> (S.insert x S.empty) `S.union` y ) S.empty xs
fPvar (If p1 p2 p3) = fPvar p1 `S.union` fPvar p2 `S.union` fPvar p3
fPvar (ProgPos p p1) = fPvar p1
data Prog = Name VName
          | Applica Prog Prog
          | Abs [VName] Prog
          | Match Prog [(VName, [Prog], Prog)]
          | Let [(VName, Prog)] Prog
          | If Prog Prog Prog
            -- Formula at Surface
          | TForall VName Prog
          | TImply Prog Prog
          | TIota VName Prog
          | TIn Prog Prog
          | TSApp Prog Prog
          | TSTApp Prog Prog
            -- tactic at Surface
          | TMP Prog Prog -- mp p1 by p2
          | TInst Prog Prog -- inst p1 by p2
          | TUG VName Prog     -- ug x . p
          | TCmp Prog          -- cmp p
          | TInvCmp Prog Prog  -- invcmp p from F
          | TSimpCmp Prog          -- cmp p
          | TInvSimp Prog Prog  -- invcmp p from F
          | TBeta Prog            -- beta p
          | TInvBeta Prog Prog  -- invbeta p from F
          | TDischarge VName (Maybe Prog) Prog -- discharge a : F . p
          | AppPre Prog Prog -- p F
            
          | ProgPos SourcePos Prog
            
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
data TScheme = Scheme [VName] FType deriving (Show)
freeVar :: FType -> [VName]
freeVar (FVar x) = [x]
freeVar (Arrow f1 f2) = (freeVar f1) ++ (freeVar f2)
freeVar (FCons x args) = x : concat (helper args)
  where helper as = map h1 as
        h1 (ArgType f) = freeVar f
        h1 (ArgProg p) = []



farity :: FType -> Int
farity (FVar _) = 0
farity (FCons _ _) = 0
farity (Arrow f1 f2) = 1 + farity f2
farity (Pi x f1 f2) = 1 + farity f2
farity (FTPos pos f) = farity f

data Datatype =
  Data VName [VName] [(VName,FType)]    
  deriving (Show)

data Module = Module VName [Decl] deriving (Show)

-- type Pattern = Prog

data Decl = ProgDecl VName Prog
          | PatternDecl VName [Prog] Prog
          | ProofDecl VName (Maybe VName) ProofScripts Prog
          | DataDecl SourcePos Datatype Bool
            -- no forall n :: Nat . P (F n), where F is a "function" take in n return a formula
          | SetDecl VName Prog
          | TacDecl VName [VName] (Either Prog ProofScripts)
          | FormOperatorDecl String Int String
          | ProgOperatorDecl String Int String
          | ProofOperatorDecl String Int String
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
fv (MP p1 p2) = fv p1 `S.union` fv p2
fv (Inst p1 t) = fv p1 `S.union` fv t
fv (UG a p) = S.delete a (fv p)
fv (Discharge a Nothing p) = S.delete a (fv p)
fv (Discharge a (Just b) p) = S.delete a (fv p) `S.union` fv b
fv (Cmp p) = fv p
fv (Beta p) = fv p
fv (InvCmp p1 t) = fv p1 `S.union` fv t
fv (InvBeta p1 t) = fv p1 `S.union` fv t
fv (Pos _ p) = fv p

-- get free set var
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

-- only for prog term and formula term comparison
-- we don't want to compare to proof term at all
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

plus1 = map $ \(x, y) ->(x, y + 1)

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

subst p (PVar x) (MP p1 p2) = do
  a1 <- subst p (PVar x) p1
  a2 <- subst p (PVar x) p2
  return $ MP a1 a2
  
subst p (PVar x) (Inst p1 t) = do
  a <- subst p (PVar x) p1
  a1 <- subst p (PVar x) t
  return $ Inst a a1
  
subst p (PVar x) (UG y p1) =
  if x == y || not (x `S.member` fv p1) then return $ UG y p1
  else if not (y `S.member` fv p)
       then do
         c <- subst p (PVar x) p1
         return $ UG y c
       else do
         n <- get
         modify (+1)
         c1 <- subst (PVar (y++ show n)) (PVar y) p1
         c2 <- subst p (PVar x) c1
         return $ UG (y++ show n) c2
                                     
subst p (PVar x) (Cmp p1) =
  subst p (PVar x) p1 >>= \ a -> return $ Cmp a
                                     
subst p (PVar x) (InvCmp p1 t) = do
  a <- subst p (PVar x) p1
  a1 <- subst p (PVar x) t
  return $ InvCmp a a1

subst p (PVar x) (Beta p1) =
  subst p (PVar x) p1 >>= \a -> return $ Beta a
                                    
subst p (PVar x) (InvBeta p1 t) = do
  a <- subst p (PVar x) p1
  a1 <- subst p (PVar x) t
  return $ InvBeta a a1

subst p (PVar x) (Discharge y (Just t) p1) = do
  t1 <- subst p (PVar x) t
  if x == y || not (x `S.member` fv p1)
    then return $ Discharge y (Just t1) p1
    else if not (y `S.member` fv p)
         then do
           c <- subst p (PVar x) p1
           return $ Discharge y (Just t1) c
         else do
           n <- get
           modify (+1)
           c1 <- subst (PVar (y++ show n)) (PVar y) p1
           c2 <- subst p (PVar x) c1
           return $ Discharge (y++ show n) (Just t1) c2

subst p (PVar x) (Discharge y Nothing p1) = 
  if x == y || not (x `S.member` fv p1) then return $ Discharge y (Nothing) p1
  else if not (y `S.member` fv p)
       then do
         c <- subst p (PVar x) p1
         return $ Discharge y (Nothing) c
       else do
         n <- get
         modify (+1)
         c1 <- subst (PVar (y++ show n)) (PVar y) p1
         c2 <- subst p (PVar x) c1
         return $ Discharge (y++ show n) (Nothing) c2
subst s (PVar x) (Pos _ f) = subst s (PVar x) f

partition f [] = []
partition f (x:[]) = [[x]]
partition f (x:x1:xs) | f x == f x1 = tack x (partition f (x1:xs))
                      | otherwise = [x]: partition f (x1:xs)
  where tack x xss = (x : head xss) : tail xss

              
