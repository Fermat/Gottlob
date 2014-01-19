module vector where

-- data Nat where
--  z :: Nat
--  s :: Nat -> Nat


data Vec U a where
   vnil :: Vec U z

-- data Vec U a where
--    vcons :: (n :: Nat) -> U -> Vec U n -> Vec U (s n) 
