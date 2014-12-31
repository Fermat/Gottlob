module fibo where

prog infixr 10 @
--prog infixl 10 +
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

-- This observer approach is isomorphic to plain approach, 
-- which implies that nothing is gained.
-- data Observer where
--   head ::  Observer
--   tail :: Observer -> Observer
--  deriving Ind

fib' zero = zero
fib' (succ zero) = succ zero
fib' (succ (succ o')) = plus (fib' (succ o')) (fib' o')
   
plus zero m = m
plus (succ n) m = succ (plus n m)
strictPlus = \ x y . ob (plus x y)
one = succ zero

tail nil = nil
tail (a @ as) = as

-- repeat a o = case o of  
--                getHead f -> f a
--                getTail o' -> repeat a o'

-- fib' o = case o of  
--            head -> zero
--            tail head -> (succ zero)
--            tail (tail o') -> plus (fib' (tail o')) (fib' o')

zipWith f (a @ as) (b @ bs) = f a b @ zipWith f as bs
zipWith f c e = nil

fibs = zero @ one @ zipWith plus fibs (tail fibs)

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

-- ultimate extesionality, Gottlob is not able to prove that:
-- forall n . n :: Nat -> Eq (fibs !! n) (fib' n)
-- If we are able prove this in Gottlob, then, we basically have an answer for 
-- the foundation of mathematics. And I don't think we have one, and I don't
-- think we could have one. So proof by pessimistic, I claim
-- Gottlob can not reason about *any* intensional behavior of infinite object. 


-- I revised my previous belief. We can indeed prove the following theorem
-- by induction on n. 
-- IH: fib !! n + fib !! n+1 = fib !! n+2
-- show fib !! (n+1) + fib !! n+2 = fib !! n+3
-- fib !! (n+3) = (zipWith + fibs (tail fibs)) !! (n+1) = fibs  !! (n+1) + tail fibs !! n+1
-- = fibs  !! (n+1) +  fibs !! n+2
-- in fact, the whole argument does not use IH at all. 
theorem fibb . forall n . n :: Nat -> Eq (plus (fibs !! n ) (fibs !! succ n)) (fibs !! succ (succ n))
proof
  b0 = byEval ((fib' (succ (succ (succ (succ zero)))))) zero
  b = byEval ( (fibs !! (succ (succ (succ (succ zero)))))) (zero)
qed