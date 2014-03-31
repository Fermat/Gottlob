module avl where
---- library code, man, I should implement a module system...
prog infixl 6 +
prog infixr 10 @

Eq a b = forall C . a :: C -> b :: C

data Nat where
  zero :: Nat
  succ :: Nat -> Nat 
  deriving Ind

data List U where
  nil :: List U
  (@) :: U -> List U -> List U


map f nil = nil
map f (x @ xs) =  f x @ map f xs

foldr f a nil = a
foldr f a (x @ xs) = f x (foldr f a xs)

(+) zero m = m
(+) (succ n) m = n + succ m

tactic chain t ls = 
       ug Q. discharge a : t :: Q . 
          let insts = map (\ x . inst (cmp x) by Q) ls
              in foldr (\ x y . mp x by y) a insts

tactic byEval t1 t2 =   
   [c] : t1 :: Q
   c1 = invbeta beta c : t2 :: Q
   c3 = ug Q . discharge c . c1
   c5 = invcmp c3 : Eq t1 t2

--------------- actual code---
-- Hurray, find a bug in inductive derivation
-- and inductive set construction... .Ahhhh!!!!
data Tree U where
  leaf :: Tree U
  node ::  Tree U -> U -> Tree U -> Tree U
  deriving Ind

-- theorem test . Eq a b
-- proof
-- indTree = ug U . (ug Tree0 . (discharge a0 : leaf :: Tree0 U . (discharge a1 : forall x . x :: Tree0 U -> forall x0 . x0 :: U -> forall x0 . x0 :: Tree0 U -> node x x0 x0 :: Tree0 U . (ug x . (discharge a2 : x :: Tree U . (mp (mp (inst (cmp a2) by Tree0) by (cmp a0)) by (cmp a1)))))))
--   : forall U . forall Tree0 . leaf :: Tree0 U -> (forall x . x :: Tree0 U -> forall x0 . x0 :: U -> forall x0 . x0 :: Tree0 U -> node x x0 x0 :: Tree0 U) -> forall x . x :: Tree U -> x :: Tree0 U
  
-- qed