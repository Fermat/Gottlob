
module Language.Syntax where
import qualified Data.Set as S
import Control.Monad.Reader
import Data.List
import Control.Monad.State.Lazy

type VName = String

data Term = Var VName
          | Lam VName Term
          | App Term Term
          deriving (Show)

-- nameless term
data TNameless = B Int
              | A TNameless TNameless
              | L TNameless
              deriving (Show, Eq)

-- extensional type, type have interpretation as set in ZF.
data EType = Ind
           | Form
           | To EType EType
           deriving (Show, Eq)

-- meta term, represent Church's simple type theory
data Meta = MVar VName EType
          | Forall VName EType Meta
          | Imply Meta Meta
          | Iota VName EType Meta
          | TIn Term Meta
          | MIn Meta Meta
          deriving (Show)

-- nameless meta term
data MNameless = V Int
             | FA MNameless
             | TI TNameless MNameless
             | MI MNameless MNameless
             | Imp MNameless MNameless
             | I MNameless
             deriving (Show, Eq)

data Proof = Assume VName Meta
           | PrVar VName
           | MP Proof Proof
           | TApp Proof Term
           | MApp Proof Meta
           | UG VName EType Proof
           | Beta Proof
           | Cmp Proof
           | InvBeta Proof
           | InvCmp Proof
           | Discharge VName Proof
           deriving (Show)


type ProofScripts = [(VName, Proof, Meta)]

data Prog = Name VName 
          | Applica Prog Prog
          | Abs [VName] Prog
          | Match VName [(VName, [VName], Prog)]
          deriving Show

-- formal type
data FType = Base [VName]
           | Arrow FType FType
           deriving (Show, Eq)
                    
data Datatype =
  Data VName [VName] [(VName,FType)]    
  deriving (Show)

type Module = [Decl] 

data Decl = ProgDecl VName Prog
          | ProofDecl VName ProofScripts Meta
          | DataDecl Datatype
          deriving Show

fv :: Term -> S.Set VName
fv (Var x) = S.insert x S.empty
fv (App t1 t2) = fv t1 `S.union` fv t2
fv (Lam x t) = S.delete x (fv t)

mvar :: Meta -> S.Set VName
mvar (MVar x _) = S.insert x S.empty
mvar (Imply f1 f2) = mvar f1 `S.union` mvar f2
mvar (Forall x _ f) = S.delete x (mvar f)
mvar (TIn t s) = fv t `S.union` (mvar s)
mvar (MIn t s) = mvar t `S.union` (mvar s)
mvar (Iota x _ s) = S.delete x (mvar s)

type GVar a = State Int a

-- Curry's Substitution, renaming only when necessary, yay!
-- will need to extend to handle formula and set as well.

subst :: Term -> Term -> Term -> GVar Term
subst t (Var x) (Var y) = return $ if x == y then t else Var y
subst t (Var x) (App t1 t2) = do
  a1 <- subst t (Var x) t1
  a2 <- subst t (Var x) t2
  return $ App a1 a2
-- Notice this definition is still inefficient, could be improved. 
subst t (Var x) (Lam y t1) = 
  if x == y then return $ Lam y t1
  else if not (x `S.member` fv t1) || not (y `S.member` fv t)
       then do
         a <- subst t (Var x) t1
         return $ Lam y a
       else 
         do
           n <- get
           modify (+1)
           a <- subst (Var ("v"++ show n)) (Var y) t1
           b <- subst t (Var x) a
           return $ Lam ("v"++ show n) b

type BindCxt a = Reader [(VName, Int)] a

plus1 = Data.List.map (\x ->(fst x,snd x + 1))

debruijn :: Term -> BindCxt TNameless
debruijn (Var x) = do 
  Just n <- asks (lookup x) 
  return $ B n
debruijn (App t1 t2) = do
  a1 <- debruijn t1
  a2 <- debruijn t2
  return $ A a1 a2
debruijn (Lam x t) = do 
  a <- local (((x,0):) . plus1) $ debruijn t 
  return $ L a
--    where plus1 = Data.List.map (\x ->(fst x,snd x + 1))

alphaEq :: Term -> Term -> Bool
alphaEq t1 t2 =
  if fv t1 == fv t2
  then
    let t1' = S.foldl' (\t x -> Lam x t) t1 (fv t1)
        t2' = S.foldl' (\t x -> Lam x t) t2 (fv t1) in
    runReader (debruijn t1') [] == runReader (debruijn t2') []
  else False

--al = alphaEq (Lam "x" (Var "x")) (Lam "z" (Var "z"))

-- wiki = Lam "z" (App (Lam "y" (App (Var "y") (Lam "x" (Var "x")))) (Lam "x" (App (Var "z") (Var "x"))))

debruijnMeta :: Meta -> BindCxt MNameless
debruijnMeta (MVar x t) = do 
  Just n <- asks (lookup x) 
  return $ V n

debruijnMeta (Forall x t f) = do 
  a <- local (((x,0):) . plus1) $ debruijnMeta f 
  return $ FA a

debruijnMeta (Imply f1 f2) = do
  a1 <- debruijnMeta f1
  a2 <- debruijnMeta f2
  return $ Imp a1 a2

debruijnMeta (TIn t s) = do
  a <- debruijn t
  b <- debruijnMeta s
  return $ TI a b

debruijnMeta (MIn b1 b2) = do
  a <- debruijnMeta b1
  a1 <- debruijnMeta b2
  return $ MI a a1

debruijnMeta (Iota x t f) = do
  a <- local (((x,0):) . plus1) $ debruijnMeta f 
  return $ I a

alphaMeta :: Meta -> Meta -> Bool
alphaMeta t1 t2 =
  if mvar t1 == mvar t2
  then
    let t1' = S.foldl' (\t x -> Forall x Ind t) t1 (mvar t1)
        t2' = S.foldl' (\t x -> Forall x Ind t) t2 (mvar t1) in
    runReader (debruijnMeta t1') [] == runReader (debruijnMeta t2') []
  else False


instance Eq Term where
  t1 == t2 = t1 `alphaEq` t2

instance Eq Meta where
  t1 == t2 = t1 `alphaMeta` t2

testform =  (TIn (Var "x") (MVar "nat" Ind)) == (TIn (Var "x") (MVar "nat" Ind))


-- [M/X]M
substMeta :: Meta -> Meta -> Meta -> GVar Meta
substMeta s (MVar x t1) (MVar y t2) =
  if x == y && t1 == t2
  then return s else return $ MVar y t2
                               
substMeta s (MVar x t) (Imply f1 f2) = do
  c1 <- substMeta s (MVar x t) f1
  c2 <- substMeta s (MVar x t) f2
  return $ Imply c1 c2

substMeta s (MVar x t) (TIn t1 set) =  do
  c <- substMeta s (MVar x t) set
  return $ TIn t1 c

substMeta s (MVar x t) (MIn t1 bin) =  do
  b <- substMeta s (MVar x t) t1
  c <- substMeta s (MVar x t) bin
  return $ MIn b c

substMeta s (MVar x t) (Forall a t1 f) =
  if x == a then return $ Forall a t1 f
    else if not (x `S.member` mvar f) || not (a `S.member` mvar s)
         then do
           c <- substMeta s (MVar x t) f
           return $ Forall a t1 c
         else
           do
             n <- get
             modify (+1)
             c1 <- substMeta (MVar (a++ show n) t) (MVar a t) f
             c2 <- substMeta s (MVar x t) c1
             return $ Forall (a++ show n) t c2

substMeta s (MVar x t) (Iota a t1 f) =
  if x == a then return $ Iota a t1 f
    else if not (x `S.member` mvar f) || not (a `S.member` mvar s)
         then do
           c <- substMeta s (MVar x t) f
           return $ Iota a t1 c
         else
           do
             n <- get
             modify (+1)
             c1 <- substMeta (MVar (a++ show n) t) (MVar a t) f
             c2 <- substMeta s (MVar x t) c1
             return $ Iota (a++ show n) t c2

-- [t/x]M
substTm :: Term -> Term -> Meta -> GVar Meta
substTm s (Var x) (MVar y t) = return $ MVar y t
substTm s (Var x) (Iota v t set) = do
  c <- fvarSubSet s (FVar x) set
  return $ Iota2 v c

-- fvarSubSet :: Formula -> Formula -> Set -> GVar Set
-- fvarSubSet s (FVar x) (SVar y) = return $ SVar y
-- fvarSubSet s (FVar x) (Iota v f) = do
--   c <- fvarSubFm s (FVar x) f
--   return $ Iota v c

-- -- [t/x]F
-- varSubFm :: Term -> Term -> Formula -> GVar Formula
-- varSubFm s (Var x) (FVar y) = return $ FVar y
-- varSubFm s (Var x) (Forall a f) = do
--   if x == a then return $ Forall a f
--     else if not (x `S.member` fvar f) || not (a `S.member` fv s)
--          then do
--            c <- varSubFm s (Var x) f
--            return $ Forall a c
--          else
--            do
--              n <- get
--              modify (+1)
--              c1 <- varSubFm (Var ("v"++ show n)) (Var a) f
--              c2 <- varSubFm s (Var x) c1
--              return $ Forall ("v"++ show n) c2

-- varSubFm s (Var x) (Pi0 a f) = do
--   c <- varSubFm s (Var x) f
--   return $ Pi0 a c

-- varSubFm s (Var x) (Pi1 a f) = do
--   c <- varSubFm s (Var x) f
--   return $ Pi1 a c
  
-- varSubFm s (Var x) (In t set) = do
--   a <- subst s (Var x) t
--   c <- varSubSet s (Var x) set
--   return $ In a c

-- varSubFm s (Var x) (BIn t t1 bin) = do
--   a <- subst s (Var x) t
--   a1 <- subst s (Var x) t1
--   c <- varSubBin s (Var x) bin
--   return $ BIn a a1 c

-- varSubFm s (Var x) (Imply f1 f2) = do
--   c1 <- varSubFm s (Var x) f1
--   c2 <- varSubFm s (Var x) f2
--   return $ Imply c1 c2 

-- varSubBin :: Term -> Term -> Binary -> GVar Binary
-- varSubBin s (Var x) (BVar y) = return $ BVar y
-- varSubBin s (Var x) (Iota2 a set) = do
--   if x == a then return $ Iota2 a set
--     else if not (x `S.member` svar set) || not (a `S.member` fv s)
--          then do
--            c <- varSubSet s (Var x) set
--            return $ Iota2 a c
--          else
--            do
--              n <- get
--              modify (+1)
--              c1 <- varSubSet (Var ("v"++ show n)) (Var a) set
--              c2 <- varSubSet s (Var x) c1
--              return $ Iota2 ("v"++ show n) c2


-- varSubSet :: Term -> Term -> Set -> GVar Set
-- varSubSet s (Var x) (SVar y) = return $ SVar y
-- varSubSet s (Var x) (Iota a f) = do
--   if x == a then return $ Iota a f
--     else if not (x `S.member` fvar f) || not (a `S.member` fv s)
--          then do
--            c <- varSubFm s (Var x) f
--            return $ Iota a c
--          else
--            do
--              n <- get
--              modify (+1)
--              c1 <- varSubFm (Var ("v"++ show n)) (Var a) f
--              c2 <- varSubFm s (Var x) c1
--              return $ Iota ("v"++ show n) c2


              
