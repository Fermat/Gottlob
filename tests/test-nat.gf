module nat where

prog infixr 9 !
-- special infix 7 ==

(!) a b = a b

Eq a b = forall C . a :: C -> b :: C

data Nat where
  z :: Nat
  s :: Nat -> Nat 

add n m = 
  case n of
     z -> m 
     s n'-> s ! add n' m

theorem ind . forall C. z :: C -> (forall y . y :: C -> s y :: C) -> (forall m . m :: Nat -> m :: C)
proof  
       [a1] : z :: C
       [a2] : forall y . y :: C -> s y :: C
       [a3] : m :: Nat
       b1 = cmp a3 : forall C . z :: C -> (forall y . y :: C -> s y :: C) -> m :: C
       b2 = inst b1 C : z :: C -> (forall y .y:: C  -> s y :: C) -> m :: C
       b3 = mp b2 a1 : (forall y. y :: C -> s y :: C) -> m :: C
       b4 = mp b3 a2 : m :: C
       b5 = discharge a3 b4 : m :: Nat -> m :: C
       b6 = ug m b5 : forall m. m :: Nat -> m :: C
       b7 = discharge a2 b6 : (forall y. y :: C -> s y :: C) -> forall m . m :: Nat -> m :: C
       b8 = discharge a1 b7 : z::C -> (forall y. y :: C -> s y :: C) -> forall m . m :: Nat -> m :: C
       b9 = ug C b8 : forall C. z::C -> (forall y.  y :: C -> s y :: C) -> forall m . m :: Nat -> m :: C
qed

theorem cong . forall f a b. Eq a b -> Eq (f a) (f b)
proof 
 [a] : Eq a b
 b = cmp a : forall C . a :: C -> b :: C
 b1 = cmp $ inst b $ iota q. Eq (f a) (f q) : (forall C . f a :: C -> f a :: C) -> forall C . f a :: C -> f b :: C
 [c] : f a :: C
 d = discharge c c : f a :: C -> f a :: C
 e = mp b1 $ ug C d : forall C . f a :: C -> f b :: C
 f = invcmp e : Eq (f a) (f b)
 q = ug f (ug a (ug b (discharge a f))) : forall f . forall a . forall b . Eq a b -> Eq (f a) (f b)
qed

theorem plus0. forall n . n :: Nat -> Eq (add n z) n 
proof 
   [a] : n :: Nat
   b1 = cmp a : forall C . z :: C -> (forall y . y :: C -> s y :: C) -> n :: C
--   b2 =  :
   
   -- (forall C . add z z :: C -> z :: C) -> (forall y . (forall C . add y z :: C -> y :: C) -> forall C . add (s y) z :: C -> s y :: C) -> forall C . add n z :: C -> n :: C
   b3 = invcmp (cmp (inst b1 (iota q. Eq (add q z) q))) : 
                             Eq (add z z) z -> (forall y. Eq (add y z) y
                                          -> Eq (add (s y) z) (s y)) -> Eq (add n z) n 
   [c] : (add z z) :: Q
--   [c0] : (\ z . \ s. z) :: Q
   -- c3 = beta c0 : \ z . \ s . z :: Q
   c4 = beta c : (\ z . \ s. z) :: Q
   c1 = invbeta c4 :  z :: Q
   c3 = ug Q $(discharge c c1) : forall Q. (add z z) :: Q -> z :: Q   --problem with nested tacti
   c5 = invcmp c3 : Eq (add z z) z
   c6 = mp b3 c5 : (forall y. Eq (add y z) y
                                        -> Eq (add (s y) z) (s y)) -> Eq (add n z) n 
   [d] : Eq (add y z) y
   [d1] : add (s y) z :: Q
   e = inst (inst (inst cong s) (add y z)) y : Eq (add y z) y -> Eq (s (add y z)) (s y)
   e1 = mp e d : Eq (s (add y z)) (s y)
   e2 = inst (cmp e1) Q : s (add y z) :: Q -> s y :: Q
   d2 = invbeta (beta d1) : s (add y z) :: Q
   d3 = mp e2 d2 : s y :: Q
   d4 = invcmp (ug Q (discharge d1 d3)) : Eq (add (s y) z) (s y)
   d5 = ug y (discharge d d4) : forall y . Eq (add y z) y -> Eq (add (s y) z) (s y)
   d6 = ug n (discharge a (mp c6 d5)) : forall n . n :: Nat -> Eq (add n z) n
-- need to make sure that proof names doesn't collapse   
-- and we can program with the proof, thus we could have tactic build-in for the proofs. yay!
qed