module vector where

data Nat where
   z :: Nat 
   s :: Nat -> Nat 

data Vec U a where
     vnil :: Vec U z
     vcons ::  (n::Nat) -> U -> Vec U n -> Vec U (s n)

data Ob A R where
 ohead :: (A -> R) -> Ob A R -> O (A -> A)
 otail :: Ob A R -> Ob A R