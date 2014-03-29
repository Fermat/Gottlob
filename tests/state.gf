module state where
prog infixr 10 >>=
prog infixr 10 >>-
formula infixl 3 *

(*) U V = forall Y . (U -> V -> Y) -> Y
Eq a b = forall C . a :: C -> b :: C

tactic and U V p1 p2 = ug Y . discharge x : U -> V -> Y . mp (mp x by p1) by p2
theorem product[Prod] . forall A B . A -> B -> A * B
proof
  [a1] : A
  [a2] : B
  c0 = and A B a1 a2 
  c = ug A . ug B . discharge a1 . discharge a2 . c0
  d = invcmp c from Prod
qed

data List U where
  nil :: List U
  cons :: U -> List U -> List U

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
tactic first U V p = mp cmp (inst (cmp p) by U) by cmp (discharge x : U . discharge y : V . x)

tactic second U V p = mp cmp (inst (cmp p) by V) by cmp (discharge x : U . discharge y : V . y)


--tick =  bindSt getSt (\ x . bindSt (putSt (plus1 x)) (\ y . (returnSt x)))
theorem surZ . zero :: Nat
proof
     [a0] : zero :: C
     [a1] : forall y . y :: C -> succ y :: C
     c = ug C . (discharge a0 . discharge a1 . a0)
     d = invcmp c : zero :: Nat
qed

theorem surSuc . forall n . n :: Nat -> succ n :: Nat
proof
  [a] : n :: Nat
  b = inst (cmp a) by C
  [a1] : zero :: C
  [a2] : forall x . x :: C -> succ x :: C
  c1 = mp (mp b by a1) by a2
  c2 = inst a2 by n
  c3 = mp c2 by c1
  c4 = ug C . discharge a1 . (discharge a2 . c3)
  c5 = invcmp c4 from succ n :: Nat
  c6 = ug n . discharge a . c5
qed

theorem weakInd . forall C . zero :: C -> (forall y. y :: Nat * y :: C -> succ y :: C) -> 
                       forall m . m :: Nat -> m :: C
proof
   [a1] : zero :: C
   [a2] : forall y. y :: Nat * y :: C -> succ y :: C
   c1 = simpCmp inst indNat by (iota z . z :: Nat * z :: C)
   base = invcmp cmp (and (zero :: Nat) (zero :: C) surZ a1) : zero :: Nat * zero :: C
   [ih] : x :: Nat * x :: C
   b = mp (inst a2 by x) by ih
   b1 = inst surSuc by x
   c = first (x :: Nat) (x :: C) ih
   c2 = invcmp c : x :: Nat
   c3 = mp b1 by c2
   d = invcmp cmp and (succ x :: Nat) (succ x :: C) c3 b : succ x :: Nat * succ x :: C
   d1 = ug x . discharge ih . d
   e1 = mp mp c1 by base by d1 
   f = inst e1 by m
   [f1] : m :: Nat
   f2 = mp f by f1
   f3 = second (m :: Nat) (m :: C) f2
   f4 = ug m . discharge f1 . f3
   f5 = ug C . discharge a1 . discharge a2 . f4
   -- show succ x :: Nat * succ x :: C
qed
                       

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

map f nil = nil
map f (cons x xs) = cons (f x) (map f xs)

foldr f a nil = a
foldr f a (cons x xs) = f x (foldr f a xs)

tactic chain t ls = 
       ug Q. discharge a : t :: Q . 
          let insts = map (\ x . inst (cmp x) by Q) ls
              in foldr (\ x y . mp x by y) a insts

tactic useCong f a b p = mp (inst inst inst cong by f by a by b) by p

tactic useSym a b p = mp (inst inst sym by a by b) by p

theorem sym . forall a b . Eq a b -> Eq b a
proof
        [c] : Eq a b
        c1 = cmp c : forall C . a :: C -> b :: C
        c2 = cmpinst c1 (iota x . x :: Q -> a :: Q )
        d = id (a :: Q)
        d1 = invcmp ug Q . mp c2 by d : Eq b a
        r = ug a . ug b. discharge c . d1
qed

theorem testH . forall n m . n :: Nat -> Eq (succ (h n m)) (h n (succ m))
proof
  a = simpCmp inst indNat by (iota z . forall m . Eq (succ (h z m)) (h z (succ m)))
  b =  byEval (h zero m) m
  b1 = useCong succ (h zero m) m b
  b2 = byEval (succ m) (h zero (succ m))
  b3 = chain (succ (h zero m)) (cons b2 (cons b1 nil))  
  b4 = ug m . invcmp b3 from Eq (succ (h zero m)) (h zero (succ m))
  [ih] : forall m . Eq (succ (h x m)) (h x (succ m))
  c0 = inst ih by (succ m) : Eq (succ (h x (succ m))) (h x (succ (succ m)))
  c2 = byEval (h (succ x) m) (h x (succ m))
  c = useCong succ (h (succ x) m) (h x (succ m)) c2
  c1 = byEval (h x (succ (succ m))) (h (succ x) (succ m)) 
  c3 = chain (succ (h (succ x) m)) (cons c1 (cons c0 (cons c nil)))
  c4 = ug m . invcmp c3 from Eq (succ (h (succ x) m)) (h (succ x) (succ m))
  c5 = ug x . discharge ih . c4
  c6 = mp (mp a by b4) by c5
  c7 = inst c6 by n
  [e] : n :: Nat
  c8 = ug n . ug m . discharge e . (inst (mp c7 by e) by m)
qed

theorem testO . forall n . n :: Nat -> Eq (ob n) n
proof 
  a = simpCmp inst weakInd by (iota z . Eq (ob z) z)
  base = byEval (ob zero) zero
  [e1] : x :: Nat * Eq (ob x) x
  e = invcmp second (x :: Nat) (Eq (ob x) x) e1 : Eq (ob x) x
  e2 = invcmp first (x :: Nat) (Eq (ob x) x) e1 : x :: Nat
  c = byEval (h x zero) (ob x) 
  c1 = invcmp chain (h x zero) (cons e (cons c nil)) : Eq (h x zero) x
  c2 = byEval (ob (succ x)) (h (succ x) zero)
  c3 = byEval (h (succ x) zero) (h x (succ zero))
  c4 = mp (inst (inst testH by x) by zero) by e2
  c5 = useSym (succ (h x zero)) (h x (succ zero)) c4
  c6 = useCong succ (h x zero) x c1
  c7 = chain (ob (succ x)) (cons c6 (cons c5 (cons c3 (cons c2 nil))))
  c8 = invcmp c7 from Eq (ob (succ x)) (succ x)
  c9 = ug x . discharge e1 . c8 
  c10 = mp (mp a by base) by c9
qed

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
                        





