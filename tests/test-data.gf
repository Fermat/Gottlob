module vector where

special infix 7 == 

data Nat where
   z :: Nat 
   s :: Nat -> Nat 

add n m = case n of
            z -> m
            s n' -> s (add n' m)
            
data Vec U a where
     vnil :: Vec U z 
     vcons ::  (n::Nat) -> U -> Vec U n -> Vec U (s n)

(==) a b = forall C. a ::C-> b::C

Sym = a == b -> b == a

-- 
-- Ha = s n 
-- A = A -> A