module vector where

-- data Nat where
--  z :: Nat 
--  s :: Nat -> Nat 

data Vec U a where
    vnil :: Vec U z
    vcons ::  Vec U n -> Vec U u

-- data Ob A R where
--  Ohead :: (A -> R) -> Ob A R
--  Otail :: Ob A R -> Ob A R