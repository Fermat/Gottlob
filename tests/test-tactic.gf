module nat where

prog infixr 9 !
prog infixr 7 ==
-- special infix 7 ==

(!) a b = a b

Eq a b = forall C . a :: C -> b :: C
ExEq f g = forall a . Eq (f a) (g a)
-- Eq a b -> ExEq a b
-- 
data Nat where
  z :: Nat
  s :: Nat -> Nat 

data Bool where
  ff :: Bool
  tt :: Bool

add n m = 
  case n of
     z -> m 
     s n'-> s (add n' m)

iszero n = case n of
             z -> tt
             s n' -> ff

(==) n m = case n of
           z -> case m of
                  z -> tt
                  s m' -> ff
           s n' -> case m of
                       z -> ff
                       s m' -> n' ==  m'
eqB n m = case n of 
            tt -> case m of
                       tt -> tt
                       ff -> ff
            ff -> case m of
                       tt -> ff
                       ff -> tt
                       
tactic id F =  discharge a : F . a     

tactic cmpinst p s = cmp inst p by s

tactic byEval t1 t2 =   
   [c] : t1 :: Q
   c1 = invbeta beta c : t2::Q
   c3 = ug Q . discharge c . c1
   c5 = invcmp c3 : Eq t1 t2

theorem isZero . Eq (iszero (add (s z) (s (s z)))) ff
proof 
  c = byEval $ (iszero (add (s z) (s (s z)))) $ ff
qed

theorem isZero1 . forall x . Eq (iszero (s x)) ff
proof 
  c = byEval $ (iszero (s x)) $ ff
  c1 = ug x . c
qed

-- theorem isZero1 . forall x . Eq (iszero (s x)) ff
-- proof 
--   c = byEval $ (iszero (s x)) $ tt : Eq (iszero (s x)) ff
--   c1 = ug x . c : forall x . Eq (iszero (s x)) ff
-- qed

theorem isZero2 . forall x . Eq (eqB (iszero (s x)) ff) tt
proof 
  c = byEval $ eqB (iszero (s x)) ff $ tt 
  c1 = ug x . c 
qed

theorem isZero3 .  Eq ((add (s z) z) == (s z)) tt
proof 
  c = byEval $ (add (s z) z) == s z $ tt
--  c1 = ug x . c : forall x . Eq ((add x z) == x) tt
qed

theorem add3eq . Eq (add (s z) (s (s z)) == s (s (s z))) tt
proof 
  c = byEval $ add (s z) (s (s z)) == s (s (s z)) $ tt 
qed

theorem add3eq' . Eq  tt (add (s z) (s (s z)) == s (s (s z)))
proof 
  c = byEval $ tt $ add (s z) (s (s z)) == s (s (s z)) 
qed

-- theorem add3 . Eq (add (s z) (s (s z)))  (s (s (s z)))
-- proof 
--   c = byEval $ add (s z) (s (s z)) $ s (s (s z)) : Eq (add (s z) (s (s z)))  (s (s (s z)))
-- qed


-- c5 = invcmp ug Q . discharge c . (invbeta beta c from t2::Q) from Eq t1 t2
--  invcmp (ug Q . (discharge c : t1 :: Q . (invbeta (beta c) from t2 :: Q))) from Eq t1 t2
theorem ind . forall C. z :: C -> (forall y . y :: C -> s y :: C) -> (forall m . m :: Nat -> m :: C)
proof  
       [a1] : z :: C
       [a2] : forall y . y :: C -> s y :: C
       [a3] : m :: Nat
       b1 = cmp a3 : forall C . z :: C -> (forall y . y :: C -> s y :: C) -> m :: C
       b2 = inst b1 by C : z :: C -> (forall y .y:: C  -> s y :: C) -> m :: C
       b3 = mp b2 by a1 : (forall y. y :: C -> s y :: C) -> m :: C
       b4 = mp b3 by a2 : m :: C
       b5 = discharge a3 . b4 : m :: Nat -> m :: C
       a6 = ug m . b5 : forall m. m :: Nat -> m :: C
       b7 = discharge a2 . a6 : (forall y. y :: C -> s y :: C) -> forall m . m :: Nat -> m :: C
       b8 = discharge a1 . b7 : z::C -> (forall y. y :: C -> s y :: C) -> forall m . m :: Nat -> m :: C
       b9 = ug C . b8 : forall C. z::C -> (forall y.  y :: C -> s y :: C) -> forall m . m :: Nat -> m :: C
qed

--id :: f::o => var => p : forall x .( f -> f)

-- b2 = {id (f a :: C) C} : forall C . f a :: C -> f b :: C           

-- ugl [ x ] p  
-- tactic ugl ls p = match ls as
--                     nil -> p
--                     x:xs -> ug x $ ugl xs p

-- byEval  =\ t1 t2 -> invcmp (ug Q $ discharge c (t1 :: Q) $ invbeta (beta c) (t2 :: Q)) $ Eq t1 t2 
-- a = {byEval t1 t2}           
-- theorem tran . forall t1 t2 t3. Eq t1 t2 -> Eq t2 t3 -> Eq t1 t3
-- .. 

-- p $ p1 $ p2
-- c1 = id f x : forall x . f -> f  ;; then first eval id f x and then proof check
theorem cong . forall f a b. Eq a b -> Eq (f a) (f b)
proof 
 [a] : Eq a b
 b = cmp a : forall C . a :: C -> b :: C
 b1 = cmpinst b (iota q. Eq (f a) (f q)): 
    (forall C . f a :: C -> f a :: C) -> forall C . f a :: C -> f b :: C
-- [c] : f a :: C --
 d = ug C . id (f a :: C) : forall C. f a :: C -> f a :: C --
 e = mp b1 by d : forall C . f a :: C -> f b :: C
 f = invcmp e : Eq (f a) (f b)
 q = ug f . ug a . ug b . discharge a . f : forall f . forall a . forall b . Eq a b -> Eq (f a) (f b)
qed

{-
theorem plus0. forall n . n :: Nat -> Eq (add n z) n 
proof 
   [a] : n :: Nat
   b1 = cmp a : forall C . z :: C -> (forall y . y :: C -> s y :: C) -> n :: C
--   b2 =  :
   
   -- (forall C . add z z :: C -> z :: C) -> (forall y . (forall C . add y z :: C -> y :: C) -> forall C . add (s y) z :: C -> s y :: C) -> forall C . add n z :: C -> n :: C
   b3 = invcmp $ cmp $ inst b1 by iota q. Eq (add q z) q : 
                             Eq (add z z) z -> (forall y. Eq (add y z) y
                                          -> Eq (add (s y) z) (s y)) -> Eq (add n z) n 
   [c] : (add z z) :: Q
--   [c0] : (\ z . \ s. z) :: Q
   -- c3 = beta c0 : \ z . \ s . z :: Q
   c4 = beta c : (\ z . \ s. z) :: Q
   c1 = invbeta c4 :  z :: Q
   c3 = ug Q $ discharge c $ c1 : forall Q. (add z z) :: Q -> z :: Q   --problem with nested tacti
   c5 = invcmp c3 : Eq (add z z) z
   c6 = mp b3 $ c5 : (forall y. Eq (add y z) y
                                        -> Eq (add (s y) z) (s y)) -> Eq (add n z) n 
   [d] : Eq (add y z) y -- IH
   [d1] : add (s y) z :: Q----pattern
   e = inst $ (inst (inst cong $ s) $ (add y z)) $ y : Eq (add y z) y -> Eq (s (add y z)) (s y)
   e1 = mp e $ d : Eq (s (add y z)) (s y) -- derived from IH
   e2 = inst $ cmp e1 $ Q : s (add y z) :: Q -> s y :: Q
   d2 = invbeta $ beta d1 : s (add y z) :: Q
   d3 = mp e2 $ d2 : s y :: Q
   d4 = invcmp $ ug Q $ (discharge d1 $ d3) : Eq (add (s y) z) (s y)
   d5 = ug y (discharge d $ d4) : forall y . Eq (add y z) y -> Eq (add (s y) z) (s y)
   d6 = ug n (discharge a $ (mp c6 $ d5)) : forall n . n :: Nat -> Eq (add n z) n
-- need to make sure that proof names doesn't collapse   
-- and we can program with the proof, thus we could have tactic build-in for the proofs. yay!
qed -}