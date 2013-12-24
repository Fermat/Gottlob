
module Language.Syntax where
import qualified Data.Set as S
import Control.Monad.Reader
import Data.List
import Control.Monad.State.Lazy

type Vname = String

data Term = Var Vname
          | Lam Vname Term
          | App Term Term
          deriving (Show)

data Nameless = B Int
              | A Nameless Nameless
              | L Nameless
              deriving (Show, Eq)

data Formless = FV Int
             | F Formless
             | P0 Formless
             | P1 Formless
             | Inn Nameless Setless
             | Im Formless Formless
             | Bin Nameless Nameless Binaryless
             deriving (Show, Eq)

data Formula = FVar Vname
             | Forall Vname Formula
             | Pi0 Vname Formula
             | Pi1 Vname Formula
             | In Term Set
             | Imply Formula Formula
             | BIn Term Term Binary
             deriving (Show)

data Setless = SV Int 
         | I Formless
         deriving (Show, Eq)

data Set = SVar Vname
         | Iota Vname Formula
         deriving (Show, Eq)

data Binaryless = BV Int
                | I2 Setless
                deriving (Show, Eq)
                         
data Binary = BVar Vname
         | Iota2 Vname Set
         deriving (Show, Eq)

data Proof = Assume Vname Formula
           | PrVar Vname
           | MP Proof Proof
           | TApp Proof Term
           | FApp Proof Formula
           | SApp Proof Set
           | UGT Vname Proof
           | UGF Vname Proof
           | UGS Vname Proof
           | ConvBeta Proof
           | ConvCmp Proof
           | InvCmp Proof
           | InvBeta Proof
           | Discharge Vname Proof
           deriving (Show, Eq)

-- Not going to adopt dependent type, reasons:
-- 1. Type inference is too expensive and may not even
-- feasible.
-- 2. If I want verfication, I may as well use G's proof system
-- to do verification.
-- 3 On the other hand, FK is way attracted. 

data Type = Arrow Type Type
          | Base Vname  -- [Applica]
          deriving (Show, Eq)

type ProofScripts = [(Vname, Proof, Formula)]

data Prog = Name Vname 
          | Applica Prog Prog
          | Abs [Vname] Prog
          | Match Vname [(Vname, [Vname], Prog)]
          deriving Show
--          | Match Vname ()

  -- [(Vname, [Applica], Applica)]

-- data Applica = AppVar Vname
--           | Comb Applica Applica
--           deriving (Show, Eq)

data Datatype = Data Vname [Vname] [(Vname,Type)]    
              deriving (Show)

type Module = [Decl] 

data Decl = ProgDecl Vname Prog
          | ProofDecl Vname ProofScripts Formula
          | DataDecl Datatype
          deriving Show

fv :: Term -> S.Set Vname
fv (Var x) = S.insert x S.empty
fv (App t1 t2) = fv t1 `S.union` fv t2
fv (Lam x t) = S.delete x (fv t)

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

type BindCxt a = Reader [(Vname, Int)] a

plus1 = Data.List.map (\x ->(fst x,snd x + 1))

debruijn :: Term -> BindCxt Nameless
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

-- al = alphaEq (Lam "x" (Var "x")) (Lam "z" (Var "z"))

-- wiki = Lam "z" (App (Lam "y" (App (Var "y") (Lam "x" (Var "x")))) (Lam "x" (App (Var "z") (Var "x"))))

debruijnForm :: Formula -> BindCxt Formless
debruijnForm (FVar x) = do 
  Just n <- asks (lookup x) 
  return $ FV n

debruijnForm (Forall x f) = do 
  a <- local (((x,0):) . plus1) $ debruijnForm f 
  return $ F a

debruijnForm (Pi0 x f) = do 
  a <- local (((x,0):) . plus1) $ debruijnForm f 
  return $ P0 a

debruijnForm (Pi1 x f) = do 
  a <- local (((x,0):) . plus1) $ debruijnForm f 
  return $ P1 a

debruijnForm (Imply f1 f2) = do
  a1 <- debruijnForm f1
  a2 <- debruijnForm f2
  return $ Im a1 a2

debruijnForm (In t s) = do
  a <- debruijn t
  b <- debruijnSet s
  return $ Inn a b

debruijnForm (BIn t t1 b) = do
  a <- debruijn t
  a1 <- debruijn t1
  c <- debruijnBin b
  return $ Bin a a1 c



debruijnSet :: Set -> BindCxt Setless
debruijnSet (SVar x) = do
  Just n <- asks (lookup x) 
  return $ SV n

debruijnSet (Iota x f) = do
  a <- local (((x,0):) . plus1) $ debruijnForm f 
  return $ I a

debruijnBin :: Binary -> BindCxt Binaryless
debruijnBin (BVar x) = do
  Just n <- asks (lookup x) 
  return $ BV n

debruijnBin (Iota2 x s) = do
  a <- local (((x,0):) . plus1) $ debruijnSet s 
  return $ I2 a

alphaForm :: Formula -> Formula -> Bool
alphaForm t1 t2 =
  if fvar t1 == fvar t2
  then
    let t1' = S.foldl' (\t x -> Forall x t) t1 (fvar t1)
        t2' = S.foldl' (\t x -> Forall x t) t2 (fvar t1) in
    runReader (debruijnForm t1') [] == runReader (debruijnForm t2') []
  else False

testform =  (In (Var "x") (SVar "nat")) == (In (Var "x") (SVar "nat"))
instance Eq Term where
  t1 == t2 = t1 `alphaEq` t2

instance Eq Formula where
  t1 == t2 = t1 `alphaForm` t2


fvar :: Formula -> S.Set Vname
fvar (FVar x) = S.insert x S.empty
fvar (Imply f1 f2) = fvar f1 `S.union` fvar f2
fvar (Forall x f) = S.delete x (fvar f)
fvar (Pi0 x f) = S.delete x (fvar f)
fvar (Pi1 x f) = S.delete x (fvar f)
fvar (In t s) = fv t `S.union` (svar s)

bvar :: Binary -> S.Set Vname
bvar (BVar x) = S.insert x S.empty
bvar (Iota2 x s) = S.delete x (svar s)

svar :: Set -> S.Set Vname
svar (SVar x) = S.insert x S.empty
svar (Iota x f) = S.delete x (fvar f)

-- [S/X^1]F 
svarSubFm :: Set -> Set -> Formula -> GVar Formula
svarSubFm s (SVar x) (FVar y) = return $ FVar y

svarSubFm s (SVar x) (Forall a f) = do
  c <- svarSubFm s (SVar x) f
  return $ Forall a c

svarSubFm s (SVar x) (Pi0 a f) = do
  c <- svarSubFm s (SVar x) f
  return $ Pi0 a c

svarSubFm s (SVar x) (Imply f1 f2) = do
  c1 <- svarSubFm s (SVar x) f1
  c2 <- svarSubFm s (SVar x) f2
  return $ Imply c1 c2

svarSubFm s (SVar x) (In t set) =  do
  c <- svarSubSet s (SVar x) set
  return $ In t c

svarSubFm s (SVar x) (BIn t t1 bin) =  do
  c <- svarSubBin s (SVar x) bin
  return $ BIn t t1 c

svarSubFm s (SVar x) (Pi1 a f) = 
  if x == a then return $ Pi1 a f
    else if not (x `S.member` fvar f) || not (a `S.member` svar s)
         then do
           c <- svarSubFm s (SVar x) f
           return $ Pi1 a c
         else
           do
             n <- get
             modify (+1)
             c1 <- svarSubFm (SVar ("V"++ show n)) (SVar a) f
             c2 <- svarSubFm s (SVar x) c1
             return $ Pi1 ("V"++ show n) c2

svarSubBin :: Set -> Set -> Binary -> GVar Binary
svarSubBin s (SVar x) (BVar y) =
  return (BVar y)
                               
svarSubBin s (SVar x) (Iota2 v s1) = do
  c <- svarSubSet s (SVar x) s1
  return $ Iota2 v c

svarSubSet :: Set -> Set -> Set -> GVar Set
svarSubSet s (SVar x) (SVar y) =
  if x == y then return s else return (SVar y)
                               
svarSubSet s (SVar x) (Iota v f) = do
  c <- svarSubFm s (SVar x) f
  return $ Iota v c

-- [F/X^0]F
fvarSubFm :: Formula -> Formula -> Formula -> GVar Formula
fvarSubFm s (FVar x) (FVar y) =
  if x == y then return s else return $ FVar y
                               
fvarSubFm s (FVar x) (Forall a f) = do
  c <- fvarSubFm s (FVar x) f
  return $ Forall a c

fvarSubFm s (FVar x) (Pi1 a f) = do
  c <- fvarSubFm s (FVar x) f
  return $ Pi1 a c

fvarSubFm s (FVar x) (Imply f1 f2) = do
  c1 <- fvarSubFm s (FVar x) f1
  c2 <- fvarSubFm s (FVar x) f2
  return $ Imply c1 c2

fvarSubFm s (FVar x) (In t set) =  do
  c <- fvarSubSet s (FVar x) set
  return $ In t c

fvarSubFm s (FVar x) (BIn t t1 bin) =  do
  c <- fvarSubBin s (FVar x) bin
  return $ BIn t t1 c

fvarSubFm s (FVar x) (Pi0 a f) =
  if x == a then return $ Pi0 a f
    else if not (x `S.member` fvar f) || not (a `S.member` fvar s)
         then do
           c <- fvarSubFm s (FVar x) f
           return $ Pi0 a c
         else
           do
             n <- get
             modify (+1)
             c1 <- fvarSubFm (FVar ("F"++ show n)) (FVar a) f
             c2 <- fvarSubFm s (FVar x) c1
             return $ Pi0 ("V"++ show n) c2

fvarSubBin :: Formula -> Formula -> Binary -> GVar Binary
fvarSubBin s (FVar x) (BVar y) = return $ BVar y
fvarSubBin s (FVar x) (Iota2 v set) = do
  c <- fvarSubSet s (FVar x) set
  return $ Iota2 v c

fvarSubSet :: Formula -> Formula -> Set -> GVar Set
fvarSubSet s (FVar x) (SVar y) = return $ SVar y
fvarSubSet s (FVar x) (Iota v f) = do
  c <- fvarSubFm s (FVar x) f
  return $ Iota v c

-- [t/x]F
varSubFm :: Term -> Term -> Formula -> GVar Formula
varSubFm s (Var x) (FVar y) = return $ FVar y
varSubFm s (Var x) (Forall a f) = do
  if x == a then return $ Forall a f
    else if not (x `S.member` fvar f) || not (a `S.member` fv s)
         then do
           c <- varSubFm s (Var x) f
           return $ Forall a c
         else
           do
             n <- get
             modify (+1)
             c1 <- varSubFm (Var ("v"++ show n)) (Var a) f
             c2 <- varSubFm s (Var x) c1
             return $ Forall ("v"++ show n) c2

varSubFm s (Var x) (Pi0 a f) = do
  c <- varSubFm s (Var x) f
  return $ Pi0 a c

varSubFm s (Var x) (Pi1 a f) = do
  c <- varSubFm s (Var x) f
  return $ Pi1 a c
  
varSubFm s (Var x) (In t set) = do
  a <- subst s (Var x) t
  c <- varSubSet s (Var x) set
  return $ In a c

varSubFm s (Var x) (BIn t t1 bin) = do
  a <- subst s (Var x) t
  a1 <- subst s (Var x) t1
  c <- varSubBin s (Var x) bin
  return $ BIn a a1 c

varSubFm s (Var x) (Imply f1 f2) = do
  c1 <- varSubFm s (Var x) f1
  c2 <- varSubFm s (Var x) f2
  return $ Imply c1 c2 

varSubBin :: Term -> Term -> Binary -> GVar Binary
varSubBin s (Var x) (BVar y) = return $ BVar y
varSubBin s (Var x) (Iota2 a set) = do
  if x == a then return $ Iota2 a set
    else if not (x `S.member` svar set) || not (a `S.member` fv s)
         then do
           c <- varSubSet s (Var x) set
           return $ Iota2 a c
         else
           do
             n <- get
             modify (+1)
             c1 <- varSubSet (Var ("v"++ show n)) (Var a) set
             c2 <- varSubSet s (Var x) c1
             return $ Iota2 ("v"++ show n) c2


varSubSet :: Term -> Term -> Set -> GVar Set
varSubSet s (Var x) (SVar y) = return $ SVar y
varSubSet s (Var x) (Iota a f) = do
  if x == a then return $ Iota a f
    else if not (x `S.member` fvar f) || not (a `S.member` fv s)
         then do
           c <- varSubFm s (Var x) f
           return $ Iota a c
         else
           do
             n <- get
             modify (+1)
             c1 <- varSubFm (Var ("v"++ show n)) (Var a) f
             c2 <- varSubFm s (Var x) c1
             return $ Iota ("v"++ show n) c2


--type Module = [Declaration] 

-- data Declaration = DeclLogic Logicdecl
--                  | DeclProof Proofdef
--                  | DeclProgdecl Progdecl           
--                  | DeclProgdef Progdef
--                  | DeclPreddef Preddef
--                  | DeclPreddecl Preddecl
--                  | DeclData Datatypedecl

-- data Declaration = ProgDecl [(Vname, [Applica], Applica)] 
--                  | SetDecl [Vname] [(Vname, Type)] -- data-name with parameters (constructor, type)
--                  | TheoremDecl Vname Formula
--                  | ProofScripts [(Vname, Proof, Formula)]
--                  deriving(Show)

--data Module = Module Vname [Declaration] deriving (Show)

-- type CombineContext = (ProgCxt, ProofContext)

-- type Context = M.Map ArgName (ArgClass, Value)

-- type DefContext = M.Map ArgName Arg

-- data Tactic = Eval
--             | Cong Term Proof
--             | Trans Proof Proof
--             | Sym Proof
--             deriving (Show, Eq)

              
