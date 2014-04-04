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

data Tree U where
  leaf :: Tree U
  node ::  Tree U -> U -> Tree U -> Tree U
  deriving Ind

