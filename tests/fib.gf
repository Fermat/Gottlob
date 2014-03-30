module fibo where

prog infixr 10 @
prog infixl 10 +
prog infixl 10 !!

Eq a b = forall C . a :: C -> b :: C

data List U where
  nil :: List U
  (@) :: U -> List U -> List U
  deriving Ind
  
data Nat where
  zero :: Nat
  succ :: Nat -> Nat 
  deriving Ind

data Observer where
  head ::  Observer
  tail :: Observer -> Observer
 deriving Ind
   
plus zero m = m
plus (succ n) m = succ (plus n m)

one = succ zero

-- tail nil = nil
-- tail (a @ as) = as

-- repeat a o = case o of  
--                getHead f -> f a
--                getTail o' -> repeat a o'

-- fib' o = case o of  
--            head -> zero
--            tail head -> (succ zero)
--            tail (tail o') -> plus (fib' (tail o')) (fib' o')

-- right, I have to fix a bug.
fib' head = zero
fib' (tail head) = succ zero
fib' (tail (tail o')) = plus (fib' (tail o')) (fib' o')

zipWith f (a @ as) (b @ bs) = f a b @ zipWith f as bs
zipWith f c e = nil

-- fibs = zero @ one @ zipWith plus fibs (tail fibs)

pred zero = zero
pred (succ n) = n

(!!) (x @ xs) zero =  x
(!!) (a @ xs) n =  xs !! pred n


tactic byEval t1 t2 =   
   [c] : t1 :: Q
   c1 = invbeta beta c : t2 :: Q
   c3 = ug Q . discharge c . c1
   c5 = invcmp c3 : Eq t1 t2

h zero m =  m
h (succ n) m = h n (succ m)

ob n = h n zero



theorem fibb . forall n . n :: Nat -> Eq (plus (fibs !! n ) (fibs !! succ n)) (fibs !! succ (succ n))
proof
  b = byEval (ob (fib' (tail (tail (tail (tail head)))))) (zero)
qed