module state where
prog infixr 10 >>=
prog infixr 10 >>-

Eq a b = forall C . a :: C -> b :: C


data Pair A B where
 times :: A -> B -> Pair A B
 
data Unit where
  unit :: Unit

data Nat where
  zero :: Nat
  succ :: Nat -> Nat 
  deriving Ind

h zero m =  m
h (succ n) m = h n (succ m)

ob n = h n zero

data State S A where
  mkState :: (S -> Pair A S) -> State S A

-- data Monad M where
--   mon :: (A )
  
returnState a = mkState (\ s . times a s)

(>>-) m k = mkState (\ s . case runState m s of
                              times a s' -> runState (k a) s')
                              
-- observer for State                              
runState (mkState f) = f  

tick' =  get >>- \ x . put (plus1 x) >>- \ y . returnState x

get = mkState (\ s . times s s)
put s = mkState (\ a . times unit s)

-- observer for Pair
fst (times a b) = a

snd (times a b) = b
plus1 n = succ n
-- State s a = s -> (a, s)
returnSt a = \ s . times a s 

(>>=) m k = \ s . case m s of
                     times a s' -> (k a) s'

getSt = \ s . times s s

putSt s' = \ s . times unit s'

-- State s a -> s -> (a, s)
runSt m s = m s

tick =  getSt >>= \ x . putSt (plus1 x) >>= \ y . returnSt x

-- tick =  getSt =>> x 
--         putSt (plus1 x) =>> y
--         returnSt x

        
-- It is all about syntactic sugar...


--tick =  bindSt getSt (\ x . bindSt (putSt (plus1 x)) (\ y . (returnSt x)))

tactic byEval t1 t2 =   
   [c] : t1 :: Q
   c1 = invbeta beta c : t2 :: Q
   c3 = ug Q . discharge c . c1
   c5 = invcmp c3 : Eq t1 t2

tactic red t1 = 
   [c] : t1 :: Q
   c1 = beta c 
   c3 = ug Q . discharge c . c1
   
theorem test0 . forall n . Eq (snd (runState tick' n)) (succ n)
proof 
  c1 = byEval (snd (runState tick' n)) (succ n)
  c2 = ug n . c1
qed

three = succ (succ (succ zero))
two = succ (succ zero)
five = succ (succ (succ (succ (succ zero))))
plus zero m = m
plus (succ n) m = succ (plus n m)

tactic cmpinst p s = cmp inst p by s 
tactic id F =  discharge a : F . a
theorem cong . forall f a b. Eq a b -> Eq (f a) (f b)
proof 
 [a] : Eq a b
 b = cmp a : forall C . a :: C -> b :: C
 b1 = cmpinst b (iota q. Eq (f a) (f q)) : 
    (forall C . f a :: C -> f a :: C) -> forall C . f a :: C -> f b :: C
 d = ug C . id (f a :: C) : forall C. f a :: C -> f a :: C 
 e = mp b1 by d : forall C . f a :: C -> f b :: C
 f = invcmp e : Eq (f a) (f b)
 q = ug f . ug a . ug b . discharge a . f : forall f . forall a . forall b . Eq a b -> Eq (f a) (f b)
qed


tactic smartCong f a b p n m = 
  -- has to rename x to x11 and y to y22 to avoid nasty variable capture problem... 
   c1 = mp (inst inst inst cong by f by a by b) by p -- : Eq (f a) (f b)
   c2 = invcmp (cmp c1) from (f a) :: (iota x11 . Eq x11 (f b))
   c3 = beta c2 : n :: (iota x11 . Eq x11 (f b))
   c4 = invcmp (cmp c3) : f b :: iota y22. ((iota x11 . Eq x11 y22) n)
   c5 = beta c4 : m :: iota y22. ((iota x11 . Eq x11 y22) n)
   c6 = invcmp (cmp c5) from Eq n m

tactic useCong f a b p = mp (inst inst inst cong by f by a by b) by p
theorem testH . forall n m . Eq (succ (h n m)) (h n (succ m))
proof
  a = simpCmp inst indNat by (iota z . forall m . Eq (succ (h z m)) (h z (succ m)))
  b =  byEval (h zero m) m
  b1 = useCong succ (h zero m) m b
  -- [ih] : Eq (h (succ x) m) (h x (succ m)) 
  -- c = byEval (h (succ (succ x)) m) (h (succ x) (succ m))

qed

{-
theorem testO . forall n . n :: Nat -> Eq (ob n) n
proof 
  a = simpCmp inst indNat by (iota z . Eq (ob z) z)
  base = byEval (ob zero) zero
  [ih] : Eq (ob x) x
--  c = byEval (ob (succ x)) (succ x)
    -- 1: [Expected Formula] x (succ zero) (\ `u3 . h `u3 (succ (succ zero))) :: Q
    -- 2: [Actual Formula] \ zero . \ succ . succ x :: Q

  c = byEval (ob x) x
qed
-}

theorem testN . forall n . Eq (ob (plus three two)) five
proof 
  a = ug n . byEval (ob (plus three two)) five
qed


theorem test1. Eq (snd (runState tick' (succ (succ zero))))  (succ (succ (succ zero))) 
proof
  a = byEval (snd (runState tick' (succ (succ zero))))  (succ (succ (succ zero))) 
--  b = byEval (runSt tick zero)  (succ (succ zero))
qed
   
theorem test. Eq (snd (runSt tick (succ (succ zero))))  (succ (succ (succ zero))) 
proof
  a = byEval (snd (runSt tick (succ (succ zero))))  (succ (succ (succ zero))) 
--  b = byEval (runSt tick zero)  (succ (succ zero))
qed
                        





