module nat where

-- prog infixr 9 !
-- prog infixr 7 ==
-- special infix 7 ==

--(!) a b = a b

Eq a b = forall C . a :: C -> b :: C
ExEq f g = forall a . Eq (f a) (g a)
Bot = forall a b . Eq a b
Emp = forall a C . a :: C 

data Nat where
  z :: Nat
  s :: Nat -> Nat 

data Bool where
  ff :: Bool
  tt :: Bool

rep n m = case n of
          z -> m
          s n' -> \ x . (rep n' (add x m))
          
data List U where
  nil :: List U
  cons :: U -> List U -> List U

add n m = 
  case n of
     z -> m 
     s n'-> s (add n' m)

iszero n = case n of
             z -> tt
             s n' -> ff

-- (==) n m = case n of
--            z -> case m of
--                   z -> tt
--                   s m' -> ff
--            s n' -> case m of
--                        z -> ff
--                        s m' -> n' ==  m'
eqB n m = case n of 
            tt -> case m of
                       tt -> tt
                       ff -> ff
            ff -> case m of
                       tt -> ff
                       ff -> tt

                       
tactic id F =  discharge a : F . a     


tactic cmpinst p s = cmp inst p by s 

tactic smartInst p s A = invcmp (cmp inst p by s) from A

tactic byEval t1 t2 =   
   [c] : t1 :: Q
   c1 = invbeta beta c : t2::Q
   c3 = ug Q . discharge c . c1
   c5 = invcmp c3 : Eq t1 t2
-- byEval invcmp (ug Q . discharge c. invbeta beta c)
theorem isZero1 . forall x . Eq (iszero (s x)) ff
proof 
  c = byEval (iszero (s x)) ff
  c1 = ug x . c
qed

theorem isZero2 . forall x . Eq (eqB (iszero (s x)) ff) tt
proof 
  c = byEval (eqB (iszero (s x)) ff) tt 
  c1 = ug x . c 
qed

-- theorem isZero3 .  Eq ((add (s z) z) == (s z)) tt
-- proof 
--   c = byEval $ (add (s z) z) == s z $ tt
-- qed

-- theorem add3eq . Eq (add (s z) (s (s z)) == s (s (s z))) tt
-- proof 
--   c = byEval $ add (s z) (s (s z)) == s (s (s z)) $ tt 
-- qed

-- theorem add3eq' . Eq tt (add (s z) (s (s z)) == s (s (s z)))
-- proof 
--   c = byEval $ tt $ add (s z) (s (s z)) == s (s (s z)) 
-- qed

tactic useTrans a b c p1 p2 = mp mp (inst inst (inst trans by a) by b by c) by p1 by p2

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

-- theorem indList .forall U .forall L . nil :: L U -> (forall x . x :: U -> y :: L U -> cons x y :: L U) -> (forall m . m :: Nat -> m :: C)
-- proof  
--  a = b
-- qed
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

tactic useCong f a b p = mp (inst inst inst cong by f by a by b) by p
-- tactic smartInst p s A = invcmp (cmp inst p by s) from A
-- tactic byInd P F base step = mp (mp (smartInst ind $ P $ F) by base) by step

tactic byInd P F base step = 
    a0 = cmpinst ind P 
    a01 = cmp base 
    a02 = cmp step 
    a03 = invcmp (mp mp a0 by a01 by a02) from F
-- (forall n . n :: Nat -> Eq (add n z) n) -> forall n . n :: Nat -> Eq (add n z) n
theorem plus0[PlusZero]. forall n . n :: Nat -> Eq (add n z) n 
proof 
    base = byEval (add z z)  z

    [as] : Eq (add y z) y -- IH
    e = (useCong s (add y z) y) as
    -- : Eq (s (add y z)) (s y)
    e2 = byEval (add (s y) z) (s (add y z))
    -- : Eq (add (s y) z) (s (add y z))
    e3 = (useTrans (add (s y) z) (s (add y z)) (s y)) e2 e
    -- : Eq (add (s y) z) (s y)
    step = ug y . (discharge as . e3)-- : forall y . Eq (add y z) y -> Eq (add (s y) z) (s y)
--    p1 = cmp id $ PlusZero : A
    a2 = byInd (iota x . Eq (add x z) x) PlusZero base step
qed

theorem plus01. forall n . n :: Nat -> Eq (add n z) n 
proof 
   [a] : n :: Nat
   
   b1 = cmp a : forall C . z :: C -> (forall y . y :: C -> s y :: C) -> n :: C

   b3 = smartInst b1 (iota q. Eq (add q z) q )
                      (Eq (add z z) z -> 
                        (forall y. Eq (add y z) y -> Eq (add (s y) z) (s y)) -> Eq (add n z) n )
   
   c5 = byEval (add z z) z : Eq (add z z) z
   
   c6 = mp b3 by c5 : (forall y. Eq (add y z) y
                                        -> Eq (add (s y) z) (s y)) -> Eq (add n z) n 
   [d] : Eq (add y z) y -- IH

   e = (useCong s (add y z) y) d : Eq (s (add y z)) (s y)

   e2 = byEval (add (s y) z) (s (add y z)) : Eq (add (s y) z) (s (add y z))
   -- 
   e3 = (useTrans (add (s y) z) (s (add y z))  (s y)) e2 e : Eq (add (s y) z) (s y)
-- tactic useTrans a b c p1 p2 = mp mp (inst inst (inst trans by a) by b by c) by p1 by p2   
   d5 = ug y . (discharge d . e3) : forall y . Eq (add y z) y -> Eq (add (s y) z) (s y)

   d6 = ug n. discharge a . mp c6 by d5 -- : forall n . n :: Nat -> Eq (add n z) n
qed 


theorem isZero. Eq (iszero (add (s z) (s (s z)))) ff
proof 
  c = byEval (iszero (add (s z) (s (s z)))) ff
qed
