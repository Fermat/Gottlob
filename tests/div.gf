module div where
---- library code, man, I should implement a module system...
prog infixl 6 +
prog infixl 6 -
prog infixl 8 <
prog infixl 8 == 
prog infixr 10 @

data Bool where
  true :: Bool
  false :: Bool
  
Eq a b = forall C . a :: C -> b :: C
Le a b = Eq (a < b) true

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

(-) zero m = zero
(-) (succ n) zero = succ n
(-) (succ n) (succ m) = n - m 

(<) zero zero = false
(<) zero (succ m) = true
(<) (succ n) zero = false
(<) (succ n) (succ m) = n < m

(==) zero zero = true
(==) zero (succ m) = false
(==) (succ n) zero = false
(==) (succ n) (succ m) = n == m

div n m = case n < m of
               true -> zero 
               false -> succ (div (n - m) m)

               
tactic chain t ls = 
       ug Q. discharge a : t :: Q . 
          let insts = map (\ x . inst (cmp x) by Q) ls
              in foldr (\ x y . mp x by y) a insts

tactic byEval t1 t2 =   
   [c] : t1 :: Q
   c1 = invbeta beta c : t2 :: Q
   c3 = ug Q . discharge c . c1
   c5 = invcmp c3 : Eq t1 t2


