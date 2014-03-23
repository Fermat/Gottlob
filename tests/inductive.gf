module basic_inductive where

prog infixr 9 $
prog infixl 9 ,
--prog pre ?

($) a b = a b

f a b = a b

Eq a b = forall C . a :: C -> b :: C
data Pair U V where
  (,) :: U -> V -> Pair U V
  deriving Ind

fst a = case a of
          (,) c d -> c
snd a = case a of
          (,) c d -> d

tactic byEval t1 t2 =   
   [c] : t1 :: Q
   c1 = invbeta beta c : t2 :: Q
   c3 = ug Q . discharge c . c1
   c5 = invcmp c3 : Eq t1 t2

-- data Li where
--   lnil :: Li
--   lcons :: forall U . U -> Li -> Li
--   deriving Ind


theorem tri . forall a b . Eq (fst (a, b)) a
proof
   c = ug a . ug b . byEval (fst (a , b)) a
qed
data Bool where
  true :: Bool
  false :: Bool
  
data List U where
  nil :: List U
  cons :: U -> List U -> List U
  deriving Ind


data Nat where
  z :: Nat
  s :: Nat -> Nat 
  deriving Ind

data Vec U a where
  vnil :: Vec U z
  vcons :: (n :: Nat) -> U -> Vec U n -> Vec U (s n)
  deriving Ind

data Observer A R where
  getHead :: (A -> R) -> Observer A R
  getTail :: Observer A R -> Observer A R 
  deriving Ind
  
add n m =  case n of
             z -> m 
             s n'-> s (add n' m)


  
-- if a then else = case a of
--                   true -> then
--                   false -> else

--  a ? b | c
-- add z m = m
-- add (s n') m = s (add n' m)

-- iszero z = tt
-- iszero (s n') = ff

-- (==) z z = tt
-- (==) (s n') (s m') = n' == m'
-- (==) z (s m') = ff
-- (==) (s n') z = ff

-- iszero n = case n of
--              z -> tt
--              s n' -> ff

-- (==) n m = case n of
--            z -> case m of
--                   z -> tt
--                   s m' -> ff
--            s n' -> case m of
--                        z -> ff
--                        s m' -> n' ==  m'

-- indVec : 
-- -- heterogeneous list for proofs
-- hCons = \ a2  a1 nil cons . cons a2 a1
-- hNil = \ nil cons . nil

{-
vec :=  iota U . iota a . iota x . 
                forall Vec . vnil :: Vec U z -> 
                (forall n . n :: Nat -> forall x . x :: U -> forall x0 . x0 :: Vec U n -> vcons n x x0 :: Vec U (s n))
                -> x :: Vec U a

ind := forall Vec U a. vnil :: Vec U z -> 
                (forall n . n :: Nat -> forall x . x :: U -> forall x0 . x0 :: Vec U n -> vcons n x x0 :: Vec U (s n))
                -> (forall m :: Vector U a -> m :: Vec U a)
                
iota U . iota a . {iota x} . forall Vec . vnil :: Vec U z -> (forall n . n :: Nat -> forall x . x :: U -> forall x0 . x0 :: Vec U n -> vcons n x x0 :: Vec U (s n)) -> x :: Vec U a

indList := [iota U . iota x .] forall List U . nil :: List U -> (forall x . x :: U -> forall x0 . x0 :: List U -> cons x x0 :: List U) -> forall (m :: LL U -> m :: List U) 
          
                    
nat := [iota x .] forall C . z :: C -> (forall x . x :: C -> s x :: C) -> {x :: C}


-- tactic deriveInd cases Ind Set = 

theorem ind . forall C. z :: C -> (forall y . y :: C -> s y :: C) -> (forall m . m :: Nat -> m :: C)
proof  
       [a0] : z :: C
       [a1] : forall y . y :: C -> s y :: C
       [a2] : m :: Nat
       b1 = cmp a2 : forall C . z :: C -> (forall y . y :: C -> s y :: C) -> m :: C
       b2 = inst b1 by C : z :: C -> (forall y . y :: C  -> s y :: C) -> m :: C
       b3 = mp b2 by a0 : (forall y. y :: C -> s y :: C) -> m :: C
       b4 = mp b3 by a1 : m :: C
       b5 = discharge a2 . b4 : m :: Nat -> m :: C
       a6 = ug m . b5 : forall m. m :: Nat -> m :: C
       b7 = discharge a1 . a6 : (forall y. y :: C -> s y :: C) -> forall m . m :: Nat -> m :: C
       b8 = discharge a0 . b7 : z :: C -> (forall y. y :: C -> s y :: C) -> forall m . m :: Nat -> m :: C
       b9 = ug C . b8 : forall C. z :: C -> (forall y.  y :: C -> s y :: C) -> forall m . m :: Nat -> m :: C
qed
-}
 -- ug C . (discharge a0 : z :: C . b7 = (discharge a1 : forall y . y :: C -> s y :: C .  a6 = (ug m . b5 = (discharge a2 : m :: Nat . b4 = (mp b3 = (mp b2 = (inst b1 = (simpCmp a2) by C) by a0) by a1)))))

-- theorem indProd . forall U V P . 
--                      (forall a. a :: U -> forall b . b :: V -> times a b :: P U V) 
--                           -> (forall x . x :: Product U V -> x :: P U V)

