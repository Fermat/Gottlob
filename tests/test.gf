module vector where

data Nat where
   z :: Nat 
   s :: Nat -> Nat 

data Vec U a where
     vnil :: Vec U z
     vcons ::  (n::Nat) -> U -> Vec U n -> Vec U (s n)


add n m = 
  case (s n) of
     z -> m
     s n'-> s (add n' m) c q

-- data Ob A R where
--   ohead :: (A -> R) -> Ob A R -> Ob A R
--   otail :: Ob A R -> Ob A R

Vec :: 
Vec U a = iota x . forall P : (Term -> Formula) -> Term -> Term -> Form . 
          vnil :: P U z -> 
          (forall y u n. u :: U -> y :: P U n -> vcons n u y :: P U (s n))
          -> x :: P U a

Vec U a = iota x . forall P :: (Term -> Formula) -> Term -> Term -> Form . 
          vnil :: P U z -> 
          (forall y u n. u :: U -> y :: P U n -> vcons n u y :: P U (s n))
          -> x :: P U a

Vec = iota U a x . forall P . vnil :: P U z -> 
          (forall y u n. u :: U -> y :: P U n -> vcons n u y :: P U (s n))
          -> x :: P U a
-- annotated
Vec = iota U:X0 a:I x:I . forall P:X1 . vnil:I :: P:X1 U:X0 z:I -> 
          (forall y:I u:I n:I. u :: U -> y :: P U n -> vcons n u y :: P U (s n))
          -> x :: P U a
-- constraits:
X1 = X0 -> I -> (I -> O)
X0 = I -> O

-- forall y. y ::C -> s y :: C
-- forall y :: C -> s y :: C xxxxxxxxxxx good
-- forall y : i . y :: C -> s y :: C  
-- forall C . P XXXX good
-- forall C => P
-- P

{-
theorem ind. forall C.Z :: C -> (forall y :: C -> S y :: C) -> (forall m :: Nat -> m :: C)
proof  
       C : Ind -> Form
       [a1] : Z::C
       [a2] : forall y :: C -> S y :: C
       [a3] : m :: Nat
       b1 = cmp a3 : forall C . Z :: C -> (forall y :: C -> S y :: C) -> m :: C
       b2 = inst b1 C : Z :: C -> (forall y :: C -> S y :: C) -> m :: C
       b3 = mp b2 a1 : (forall y :: C -> S y :: C) -> m :: C
       b4 = mp b3 a2 : m :: C
       b5 = discharge a3 b4 : m :: Nat -> m :: C
       b6 = ug m b5 : forall m :: Nat -> m :: C
       b7 = discharge a2 b6 : (forall y :: C -> S y :: C) -> forall m :: Nat -> m :: C
       b8 = discharge a1 b7 : Z::C -> (forall y :: C -> S y :: C) -> forall m :: Nat -> m :: C
       b9 = ug C b8 : forall C. Z::C -> (forall y :: C -> S y :: C) -> forall m :: Nat -> m :: C
qed
-}