module vector where

-- prog infix 7 ||

-- (||) a b = case a of
--    tt -> tt
--    ff -> b

data Nat where
   z :: Nat 
   s :: Nat -> Nat 
   
-- add n m = 
--   case (s n) of
--      z -> m n || b
--      s n'-> s (add n' m) c q


-- Vec U a = iota x . forall P . vnil :: P U z -> 
--   (forall y u n . u :: U -> y :: P U n -> vcons n u y :: P U (s n)) -> x :: P U a


theorem ind. forall C. z :: C -> (forall y. y :: C -> s y :: C) -> (forall m . m :: Nat -> m :: C)
proof  
       [a1] : z :: C
       [a2] : forall y . y :: C -> s y :: C
       [a3] : m :: Nat
       b1 = cmp a3 : forall C . z :: C -> (forall y . y :: C -> s y :: C) -> m :: C
--       b2 = inst b1 C : z :: C -> (forall y . y :: C -> s y :: C) -> m :: C
       -- b3 = mp b2 a1 : (forall y. y :: C -> s y :: C) -> m :: C
       -- b4 = mp b3 a2 : m :: C
       -- b5 = discharge a3 b4 : m :: Nat -> m :: C
       -- b6 = ug m b5 : forall m. m :: Nat -> m :: C
       -- b7 = discharge a2 b6 : (forall y. y :: C -> s y :: C) -> forall m . m :: Nat -> m :: C
       -- b8 = discharge a1 b7 : z::C -> (forall y. y :: C -> s y :: C) -> forall m . m :: Nat -> m :: C
       -- b9 = ug C b8 : forall C. z::C -> (forall y.  y :: C -> s y :: C) -> forall m . m :: Nat -> m :: C
qed

-- a4 = invcmp a3 :  F1   -- F1 --> F0
-- invcmp (invcmp a3:F1) F2 : F2 -- F2 --> F1
          
-- data Vec U a where
--      vnil :: Vec U z 
--      vcons ::  (n::Nat) -> U -> Vec U n -> Vec U (s n)


-- data Ob A R where
--   ohead :: (A -> R) -> Ob A R -> Ob A R
--   otail :: Ob A R -> Ob A R
  

{-
-- annotated
Vec = iota U:X0 a x . forall P:X1 . vnil :: P:X1 U:X0 z:I -> 
          (forall y u n. u :: U -> y :: P U n -> vcons n u y :: P U (s n))
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
-- forall C:X0 . z :: C -> (forall y. y :: C -> s y :: C) -> (forall m . m :: Nat:X1 -> m :: C)


-}