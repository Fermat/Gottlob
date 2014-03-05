module stream where

Eq a b = forall C . a :: C -> b :: C

eq n m = case n of
           z -> case m of
                  z -> tt
                  s m' -> ff
           s n' -> case m of
                       z -> ff
                       s m' -> eq n' m'

data Nat where
  z :: Nat
  s :: Nat -> Nat 
  
data List U where
  nil :: List U
  cons :: U -> List U -> List U

add n m = 
  case n of
     z -> m 
     s n'-> s (add n' m)

ones = cons (s z) ones
 
plus1 x = add x (s z)

data Bool where
  ff :: Bool
  tt :: Bool

data Observer A R where
  getHead :: (A -> R) -> Observer A R
  getTail :: Observer A R -> Observer A R 
  
-- Stream A is a function: 
-- for any R, Observer A R -> R
ident x = x 
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
   c1 = mp (inst inst inst cong by f by a by b) by p -- : Eq (f a) (f b)
   c2 = invcmp (cmp c1) from (f a) :: (iota x . Eq x (f b))
   c3 = beta c2 : n :: (iota x . Eq x (f b))
   c4 = invcmp (cmp c3) : f b :: iota y. ((iota x . Eq x y) n)
   c5 = beta c4 : m :: iota y. ((iota x . Eq x y) n)
   c6 = invcmp (cmp c5) from Eq n m
   -- Eq n m

head s = s (getHead ident)

tail s = \ o . s (getTail o)

-- A -> Observer A R -> R
repeat a o = case o of  
               getHead f -> f a
               getTail o' -> repeat a o'

natStream a o = case o of  
                  getHead f -> f a
                  getTail o' -> natStream (plus1 a) o'

map f s o = case o of
             getHead g -> g (f (head s))
             getTail o' -> map f s o'

theorem trans . forall a b c . Eq a b -> Eq b c -> Eq a c
proof
        [m1] : Eq a b
        [m2] : Eq b c
        [m3] : a :: C
        d1 = inst cmp m1 by C 
        d2 = mp d1 by m3 
        d3 = inst cmp m2 by C   
        d4 = mp d3 by d2 
        d5 = invcmp ug C. discharge m3 . d4 : Eq a c
        -- d7 =  discharge m2 . d5 
        -- d8 = discharge m1 . d7 -- 
        d6 = ug a . ug b . ug c . discharge m1 . discharge m2 . d5 
qed

tactic useTrans a b c p1 p2 = mp mp (inst inst (inst trans by a) by b by c) by p1 by p2
             
tactic byEval t1 t2 =   
   [c] : t1 :: Q
   c1 = invbeta beta c : t2::Q
   c3 = ug Q . discharge c . c1
   c5 = invcmp c3 : Eq t1 t2
--  Observer : (i -> o) -> (i -> o) -> i -> o = 
-- iota A . iota R . iota x . forall Observer . (forall a . (forall x . x :: A -> a x :: R) -> getHead a :: Observer A R) ->  ( forall x . x :: Observer A R -> getTail x :: Observer A R) -> x :: Observer A R

theorem indOb . forall A R Ob . (forall a . (forall x . x :: A -> a x :: R) -> getHead a :: Ob A R) ->  (forall x . x :: Ob A R -> getTail x :: Ob A R) -> (forall x . x :: Observer A R -> x :: Ob A R)
proof
  [a1] : forall a . (forall x . x :: A -> a x :: R) -> getHead a :: Ob A R
  [a2] : forall x . x :: Ob A R -> getTail x :: Ob A R
  [a3] : y :: Observer A R
  b = cmp a3 
  b1 = inst b by Ob 
  b2 = mp (mp b1 by a1) by a2 
  b3 = ug y . discharge a3 . b2 
  b4 = ug A . ug R . ug Ob . discharge a1 . discharge a2 . b3 
  
qed 

tactic byInd P F base step = 
    a0 = cmpinst indOb P 
    a01 = cmp base 
    a02 = cmp step 
    a03 = invcmp (mp mp a0 by a01 by a02) from F

theorem tes0 . Eq (add z (s z)) (s z)
proof
 c = byEval  (add z (s z)) (s z)
qed

theorem tes1 . Eq (plus1 (head (repeat (s z))))  (s (s z))
proof
 b0 = byEval (plus1 (head (repeat (s z)))) (s (s z))
 -- b01 = (smartCong $ \ q z0 s1 . s1 q $ add z (s z) $ s z) b0 $ \ z0 s1 . s1 (add z (s z)) $ \ z0 s1 . s1 (s z) : Eq (\ z0 . \ s1 . s1 (add z (s z))) (\ z0 . \ s1 . s1 (s z))
 -- b = byEval $ (plus1 (head (repeat (s z)))) $ (\ z0 . \ s1 . s1 (add z (s z)))
 -- b02 = byEval  $ (\ z0 . \ s1 . s1 (s z)) $ (s (s z))
 -- b03 = (useTrans $ (plus1 (head (repeat (s z)))) $ (\ z0 . \ s1 . s1 (add z (s z))) $ (\ z0 . \ s1 . s1 (s z))) b b01 
 -- b04 = (useTrans $ (plus1 (head (repeat (s z)))) $ (\ z0 . \ s1 . s1 (s z)) $ (s (s z))) b03 b02
qed

tactic useCong f a b p = mp (inst inst inst cong by f by a by b) by p
{-
theorem ext . forall o A R . o :: Observer A R -> Eq (map plus1 (repeat (s z)) o) (repeat (s (s z)) o) 
proof
 [a1] : forall x . x :: A -> a x :: R
-- b0 = byEval $ (eq (map plus1 (repeat (s z)) (getHead id)) (repeat (s (s z)) (getHead id))) $ tt 
-- b1 = byEval $ (eq (map plus1 (repeat (s z)) (getHead a)) (repeat (s (s z)) (getHead a))) $ tt  
 b2 =  byEval $ (map plus1 (repeat (s z)) (getHead a)) $ a (plus1 (head (repeat (s z))))
 b3 = byEval $ a (s (s z)) $ (repeat (s (s z)) (getHead a))
-- a = tes1 : A
 b4 = (useCong $ a $ plus1 (head (repeat (s z))) $ s (s z)) tes1 
 b5 = (useTrans $ (map plus1 (repeat (s z)) (getHead a)) $ a (plus1 (head (repeat (s z)))) $ a (s (s z)) ) b2 b4 
 b6 = (useTrans $ (map plus1 (repeat (s z)) (getHead a)) $ a (s (s z)) $ (repeat (s (s z)) (getHead a))) b5 b3 : Eq (map plus1 (repeat (s z)) (getHead a)) (repeat (s (s z)) (getHead a))
 base = ug a . discharge a1 . b6 
 [a2] : Eq (map plus1 (repeat (s z)) x) (repeat (s (s z)) x) 
-- show Eq (map plus1 (repeat (s z)) (getTail x)) (repeat (s (s z)) (getTail x)) 
--x (\ g . g (plus1 (head (repeat (s z))))) (\ o' . map plus1 (repeat (s z)) o') :: Q
-- x (\ f . f (s (s z))) (\ o' . repeat (s (s z)) o') :: Q
-- smartCong f a b p n m
 c0 = (smartCong $ \ q o'. q o' $  map plus1 (repeat (s z)) $ repeat (s (s z))) a2 $ (\ o' . map plus1 (repeat (s z)) o') $ (\ o' . repeat (s (s z)) o') : A 
 -- Can't proceed since we don't admit functional extensionality as axiom.
 -- Eq (f x) (g x) -/-> Eq f g 
 
 c1 = byEval $ (repeat (s (s z)) x)  $ k
qed


theorem test1 . Eq (head (repeat (s z))) (repeat (s z) (getHead id)) 
proof 
  c = byEval $ (head (repeat (s z))) $ (repeat (s z) (getHead id)) 
qed

theorem test2 . Eq (head (tail (natStream (s z)))) (natStream (s z) (getTail (getHead id))) 
proof 
  c = byEval $ (head (tail (natStream (s z)))) $ (natStream (s z) (getTail (getHead id))) 
qed

-- This work!
theorem test3 . Eq (eq (head (tail (tail (natStream (s z))))) (s (s (s z)))) tt
proof 
  c = byEval $ (eq (head (tail (tail (natStream (s z))))) (s (s (s z)))) $ tt
qed

theorem test4 . Eq (eq (natStream (s z) (getTail (getTail (getHead id)))) (s (s (s z)))) tt
proof 
  c = byEval $ (eq (natStream (s z) (getTail (getTail (getHead id)))) (s (s (s z)))) $ tt
qed

-- due to laziness, it doesn't work
-- theorem test4 . Eq (natStream (s z) (getTail (getTail (getHead id)))) (s (s (s z)))
-- proof 
--   c = byEval $  (natStream (s z) (getTail (getTail (getHead id)))) $ (s (s (s z)))
-- qed

-}

