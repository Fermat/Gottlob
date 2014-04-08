module div where
---- library code, man, I should implement a module system...
prog infixl 6 +
prog infixl 6 -
prog infixl 8 <
prog infixl 8 == 
prog infixr 10 @
formula infixl 3 *
formula infixl 4 <+>

data Bool where
  true :: Bool
  false :: Bool
  deriving Ind
-- data Stream A where
--   cons :: A -> Stream A -> Stream A
--  deriving Ind 


--u b = b
--u (cons a s) = s

(*) U V = forall Y . (U -> V -> Y) -> Y  
(<+>) U V = forall Y . (U -> Y) -> (V -> Y) -> Y  

Eq a b = forall C . a :: C -> b :: C
Le a b = Eq (a < b) true
Bot = forall x y . Eq x y

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

pred zero = zero
pred (succ n) = n
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
-- FIXME: when changing the X in 'and' to Y, we got an type inference error
-- in d8 of the proof of division.
tactic and U V p1 p2 = ug X . discharge x11 : U -> V -> X . mp (mp x11 by p1) by p2
tactic first U V p = mp cmp (inst (cmp p) by U) by cmp (discharge x : U . discharge y : V . x)
tactic second U V p = mp cmp (inst (cmp p) by V) by cmp (discharge x : U . discharge y : V . y)

tactic smartFirst U V p = invcmp mp cmp (inst (cmp p) by U) by cmp (discharge x : U . discharge y : V . x) from U

tactic smartSecond U V p = invcmp mp cmp (inst (cmp p) by V) by cmp (discharge x : U . discharge y : V . y) from V

tactic inj1 U V u = ug X . discharge x : U -> X . discharge y : V -> X . mp x by u
tactic inj2 U V v = ug X . discharge x : U -> X . discharge y : V -> X . mp y by v


tactic chain t ls = 
       ug Q. discharge a : t :: Q . 
          let insts = map (\ x . inst (cmp x) by Q) ls
              in foldr (\ x y . mp x by y) a insts
 
tactic byEval t1 t2 =   
   [c] : t1 :: Q
   c1 = invbeta beta c : t2 :: Q
   c3 = ug Q . discharge c . c1
   c5 = invcmp c3 : Eq t1 t2
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
tactic useCong f a b p = mp (inst inst inst cong by f by a by b) by p

tactic smartCong f a b p n m = 
  -- has to rename x to x11 and y to y22 to avoid nasty variable capture problem... 
   c1 = mp (inst inst inst cong by f by a by b) by p -- : Eq (f a) (f b)
   c2 = invcmp (cmp c1) from (f a) :: (iota x11 . Eq x11 (f b))
   c3 = beta c2 : n :: (iota x11 . Eq x11 (f b))
   c4 = invcmp (cmp c3) : f b :: iota y22. ((iota x11 . Eq x11 y22) n)
   c5 = beta c4 : m :: iota y22. ((iota x11 . Eq x11 y22) n)
   c6 = invcmp (cmp c5) from Eq n m

tactic betterCong f a b p n m = 
-- name comes from "better call Saul"
   c1 = mp (inst inst inst cong by f by a by b) by p -- : Eq (f a) (f b)
   c2 = byEval n (f a)
   c3 = byEval (f b) m 
   c4 = invcmp chain n (c3 @ c1 @ c2 @ nil) : Eq n m 
   

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

-- s : A + B, p1 : A -> P , p2 : A -> P
tactic sumElim A B P p1 p2 = 
       [s] : A <+> B
       a1 = inst invcmp cmp s from (forall Y . (A -> Y) -> (B -> Y) -> Y) by P
       a2 = mp (mp a1 by p1) by p2
       a3 = discharge s . a2 -- from A <+> B -> P
       

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

theorem boolContra[BContra]. Eq true false -> Bot
proof
     [a] : Eq true false
     b = ug x . ug y . smartCong (\ f . f x y) true false a x y
     c = invcmp cmp discharge a . b from BContra
qed

theorem lessZero . forall y . y :: Nat -> Le y zero -> Bot
proof
        a = simpCmp inst indNat by iota z . Le z zero -> Bot
        b = byEval false (zero < zero)
        [a1] : Le zero zero
        b1 = invcmp cmp a1 : Eq (zero < zero) true
        b2 = invcmp chain false ( b1 @ b @ nil) from Eq false true
        b3 = discharge a1 . mp boolContra by useSym false true b2 
        [ih] : Le x zero -> Bot
        -- to show Le (succ x) zero -> Bot
        [a2] : Le (succ x) zero
        c1 = invcmp cmp a2 : Eq (succ x < zero) true
        c = byEval false (succ x < zero)
        c2 = invcmp chain false (c1 @ c @ nil) : Eq false true
        c3 = ug x . discharge ih . discharge a2 . mp boolContra by useSym false true c2
        end = mp mp a by b3 by c3
qed

theorem discrete . forall n y . n :: Nat -> y :: Nat -> Le y n * Le n (succ y) -> Bot
proof
         a = simpCmp inst weakInd by iota z . forall y . y :: Nat -> Le y z * Le z (succ y) -> Bot
         [a1] : y :: Nat
         [a2] : (Le y zero) * (Le zero (succ y))
         a3 = inst lessZero by y
         a4 = invcmp first (Le y zero) (Le zero (succ y)) a2 : Le y zero
         a5 = mp mp a3 by a1 by a4
         a6 = ug y . discharge a1 . discharge a2 . a5
         [b] : (y :: Nat) * (forall y0 . y0 :: Nat -> (Le y0 y) * (Le y (succ y0)) -> Bot)
         b1 = first (y :: Nat) (forall y0 . y0 :: Nat -> (Le y0 y) * (Le y (succ y0)) -> Bot) b
         b2 = invcmp b1 : y :: Nat
         b3 = second (y :: Nat) (forall y0 . y0 :: Nat -> (Le y0 y) * (Le y (succ y0)) -> Bot) b
         b4 = invcmp b3 : forall y0 . y0 :: Nat -> (Le y0 y) * (Le y (succ y0)) -> Bot
     -- to show  forall y0 . y0 :: Nat -> (*) (Le y0 (succ y)) (Le (succ y) (succ y0)) -> Bot
         ind = simpCmp inst weakInd by iota z . Le z (succ y) * Le (succ y) (succ z) -> Bot
         [c1] : (Le zero (succ y)) * (Le (succ y) (succ zero))
         c2 = invcmp second (Le zero (succ y)) (Le (succ y) (succ zero)) c1 : Eq ((succ y) < (succ zero)) true
         c3 = byEval (y < zero) (succ y < succ zero) 
         c4 = invcmp chain (y < zero) (c2 @ c3 @ nil) : Le y zero
         c5 = mp mp inst lessZero by y by b2 by c4
         c6 = discharge c1 . c5
         [d] : (y0 :: Nat) * ((Le y0 (succ y)) * (Le (succ y) (succ y0)) -> Bot)
         d2 = invcmp first (y0 :: Nat) ((Le y0 (succ y)) * (Le (succ y) (succ y0)) -> Bot) d : y0 :: Nat
     -- show: (Le (succ y0) (succ y)) * (Le (succ y) (succ (succ y0))) -> Bot
         [d1] : (Le (succ y0) (succ y)) * (Le (succ y) (succ (succ y0)))
         e1 = invcmp first (Le (succ y0) (succ y)) (Le (succ y) (succ (succ y0))) d1 : Eq ((succ y0) < (succ y)) true
         e2 = invcmp second (Le (succ y0) (succ y)) (Le (succ y) (succ (succ y0))) d1 : Eq ((succ y) < (succ (succ y0))) true 
         e3 = byEval (y0 < y) (succ y0 < succ y)                   
         e4 = invcmp chain (y0 < y) (e1 @ e3 @ nil) : Le y0 y
         e5 = byEval (y < succ y0) (succ y < (succ (succ y0)))
         e6 = invcmp chain (y < succ y0) (e2 @ e5 @ nil) : Le y (succ y0)
         e7 = invcmp cmp and (Le y0 y) (Le y (succ y0)) e4 e6 : (Le y0 y) * (Le y (succ y0))
         e8 = mp mp inst b4 by y0 by d2 by e7
         e9 = ug y0 . discharge d . discharge d1 . e8
         f1 = mp mp ind by c6 by e9         
         f2 = ug y . discharge b . f1         
         f3 = mp mp a by a6 by f2
         [g] : n :: Nat
         [g1] : y :: Nat
         f4 =  mp inst mp (inst f3 by n) by g by y by g1
         f5 = ug n . ug y . discharge g . discharge g1 . f4
qed

theorem sucY . forall y . Le zero (succ y)
proof
        a0 = invcmp cmp byEval (zero < (succ y)) true : Le zero (succ y)
        a1 = ug y . a0
qed

theorem compareZero . forall n . n :: Nat -> (Le zero n) <+> (Eq zero n)
proof
      a = simpCmp inst indNat by iota n . (Le zero n) <+> (Eq zero n)        
      a1 = byEval zero zero
      a2 = invcmp cmp inj2 (Le zero zero) (Eq zero zero) a1 : (Le zero zero) <+> (Eq zero zero)       
      [ih] : Le zero x <+> Eq zero x
      a3 = invcmp cmp inj1 (Le zero (succ x)) (Eq zero (succ x)) (inst sucY by x) : (Le zero (succ x)) <+> (Eq zero (succ x))
      a4 = ug x . discharge ih . a3
      b = mp mp a by a2 by a4
qed

-- man, this is tiresome...
theorem injective . forall n m . Eq (succ n) (succ m) -> Eq n m
proof
     [a0] : Eq (succ n) (succ m)
     a = smartCong pred (succ n) (succ m) a0 n m 
     a1 = ug n . ug m . discharge a0 . a
qed

theorem tri . forall y n . y :: Nat -> n :: Nat -> Le y n <+> Eq y n <+> Le n y
proof
    a = simpCmp inst indNat by iota y . forall n . n :: Nat -> Le y n <+> Eq y n <+> Le n y
    [a1] : n :: Nat
    a2 = mp inst compareZero by n by a1
    a3 = invcmp cmp inj1 ((Le zero n) <+> (Eq zero n)) (Le n zero) a2 : (Le zero n) <+> (Eq zero n) <+> (Le n zero)
    a4 = ug n . discharge a1 . a3
    [ih] : forall n . n :: Nat -> (Le x n) <+> (Eq x n) <+> (Le n x)    
    -- show forall n . n :: Nat -> (Le (succ x) n) <+> (Eq (succ x) n) <+> (Le n (succ x))
    b = simpCmp inst weakInd by iota n . (Le (succ x) n) <+> (Eq (succ x) n) <+> (Le n (succ x))
    b1 = inj2 ((Le (succ x) zero) <+> (Eq (succ x) zero)) (Le zero (succ x)) (inst sucY by x)
    b2 = invcmp cmp b1 : (Le (succ x) zero) <+> (Eq (succ x) zero) <+> (Le zero (succ x))
    [ih2] : (y :: Nat) * ((Le (succ x) y) <+> (Eq (succ x) y) <+> (Le y (succ x)))
    c2 = invcmp first (y :: Nat) ((Le (succ x) y) <+> (Eq (succ x) y) <+> (Le y (succ x))) ih2 : y :: Nat
    c3 = invcmp second (y :: Nat) ((Le (succ x) y) <+> (Eq (succ x) y) <+> (Le y (succ x))) ih2 : (Le (succ x) y) <+> (Eq (succ x) y) <+> (Le y (succ x))
    c1 = mp inst ih by y by c2 
    -- to show (Le (succ x) (succ y)) <+> (Eq (succ x) (succ y)) <+> (Le (succ y) (succ x))
    [d1] : Le x y
    d2 = byEval ((succ x) < (succ y)) (x < y) 
    d3 = invcmp cmp d1 : Eq (x < y) true
    d4 = invcmp chain (succ x < succ y) ( d3 @ d2 @ nil) : Le (succ x) (succ y)
    d7 = invcmp cmp inj1 (Le (succ x) (succ y)) (Eq (succ x) (succ y)) d4 : (Le (succ x) (succ y)) <+> (Eq (succ x) (succ y))
    d6 = invcmp cmp inj1 ((Le (succ x) (succ y)) <+> (Eq (succ x) (succ y))) (Le (succ y) (succ x)) d7 : (Le (succ x) (succ y)) <+> (Eq (succ x) (succ y)) <+> (Le (succ y) (succ x))
    d5 = discharge d1 . d6
    [e1] : Eq x y 
    e2 = useCong succ x y e1
    e3 = invcmp cmp inj2 (Le (succ x) (succ y)) (Eq (succ x) (succ y)) e2 : (Le (succ x) (succ y)) <+> (Eq (succ x) (succ y))
    e4 = invcmp cmp inj1 ((Le (succ x) (succ y)) <+> (Eq (succ x) (succ y))) (Le (succ y) (succ x)) e3 : (Le (succ x) (succ y)) <+> (Eq (succ x) (succ y)) <+> (Le (succ y) (succ x))
    e5 = discharge e1 . e4
    [f1] : Le y x
    f2 = byEval ((succ y) < (succ x)) (y < x) 
    f3 = invcmp cmp f1 : Eq (y < x) true
    f4 = invcmp chain (succ y < succ x) ( f3 @ f2 @ nil) : Le (succ y) (succ x)
    f6 = invcmp cmp inj2 ((Le (succ x) (succ y)) <+> (Eq (succ x) (succ y))) (Le (succ y) (succ x)) f4 : (Le (succ x) (succ y)) <+> (Eq (succ x) (succ y)) <+> (Le (succ y) (succ x))
    f5 = discharge f1 . f6
    -- g1 = let q = (Le (succ x) (succ y)) <+> (Eq (succ x) (succ y)) <+> (Le (succ y) (succ x))
    --       in inst g by q
    g2 = let q = (Le (succ x) (succ y)) <+> (Eq (succ x) (succ y)) <+> (Le (succ y) (succ x))
         in sumElim (Le x y) (Eq x y) q d5 e5
    g3 = let q = (Le (succ x) (succ y)) <+> (Eq (succ x) (succ y)) <+> (Le (succ y) (succ x))
         in sumElim ((Le x y) <+> (Eq x y)) (Le y x) q g2 f5
    g4 = mp g3 by c1
    h = ug y . discharge ih2 . g4     
    h1 = mp mp b by b2 by h
    h2 = ug x . discharge ih . h1
    h3 = mp mp a by a4 by h2
    h4 = inst h3 by y
    [h5] : y :: Nat
    h6 = inst (mp h4 by h5) by n 
    [h7] : n :: Nat
    h8 = ug y . ug n . discharge h5 . discharge h7 . mp h6 by h7
qed

theorem less . forall y n . y :: Nat -> n :: Nat -> Le y (succ n) -> Le y n <+> Eq y n
proof
        [a2] : y :: Nat
        [a1] : n :: Nat
        [b] : Le y (succ n)
        c = mp mp inst inst tri by y by n by a2 by a1         
        c1 = discharge b1 : Le y n <+> Eq y n . b1
        [c2] : Le n y
        d = invcmp cmp and (Le n y)  (Le y (succ n)) c2 b : (Le n y) * (Le y (succ n))  
        d1 = inst inst discrete by y by n
        d2 = mp mp mp d1 by a2 by a1 by d
        bot = invcmp inst inst cmp d2 by y by n : Eq y n
        e = invcmp cmp inj2 (Le y n) (Eq y n) bot : Le y n <+> Eq y n
        e1 = discharge c2 . e
        e2 = sumElim (Le y n <+> Eq y n) (Le n y) (Le y n <+> Eq y n) c1 e1 
        e3 = mp mp inst inst tri by y by n by a2 by a1
        e4 = ug y . ug n . discharge a2 . discharge a1 . discharge b . mp e2 by e3
qed

theorem strongInd . forall C . zero :: C -> 
                           (forall x. x :: Nat * (forall y .  y :: Nat * Le y x -> y :: C) 
                               -> x :: C) -> forall m . m :: Nat -> m :: C
proof
  [a1] : zero :: C
  [a2] : forall x. x :: Nat * (forall y .  y :: Nat * Le y x -> y :: C) -> x :: C
  b = simpCmp inst weakInd by (iota z . forall y .  y :: Nat * Le y z -> y :: C)
  -- show forall y . (y :: Nat) * (Le y zero) -> y :: C
  [b1] : (y :: Nat) * (Le y zero)
  b2 = invcmp second (y :: Nat) (Le y zero) b1 : Le y zero
  b4 = invcmp first (y :: Nat) (Le y zero) b1 : y :: Nat
  b3 = cmp mp mp inst lessZero by y by b4 by b2
  b5 = mp inst inst inst b3 by zero by y by C by a1
  c = ug y . discharge b1 . b5
  [ih] : (y :: Nat) * (forall y0 . (y0 :: Nat) * (Le y0 y) -> y0 :: C)
  h1 = invcmp first (y :: Nat) (forall y0 . (y0 :: Nat) * (Le y0 y) -> y0 :: C) ih : y :: Nat
  h2 = invcmp second (y :: Nat) (forall y0 . (y0 :: Nat) * (Le y0 y) -> y0 :: C) ih : forall y0 . (y0 :: Nat) * (Le y0 y) -> y0 :: C
  -- show forall y0 . (*) (y0 :: Nat) (Le y0 (succ y)) -> y0 :: C
  [c1] : (y0 :: Nat) * (Le y0 (succ y))
  c0 = invcmp first (y0 :: Nat) (Le y0 (succ y)) c1 : y0 :: Nat
  c2 = invcmp second (y0 :: Nat) (Le y0 (succ y)) c1 : Le y0 (succ y)
  c3 = mp mp mp inst inst less by y0 by y by c0 by h1 by c2
  d1 = inst h2 by y0
  [d2] : Le y0 y
  d3 = invcmp cmp and (y0 :: Nat) (Le y0 y) c0 d2 : (y0 :: Nat) * (Le y0 y)
  d4 = discharge d2 . mp d1 by d3
  e1 = mp inst a2 by y by ih
  [d3] : Eq y0 y
  d7 = mp inst cmp (useSym y0 y d3) by C by e1
  d5 = discharge d3 . d7
  d8 = sumElim (Le y0 y) (Eq y0 y) (y0 :: C) d4 d5
  d9 = ug y . discharge ih . ug y0 . discharge c1 . mp d8 by c3
  e1 = mp mp b by c by d9
  [f] : m :: Nat
  f1 = mp inst e1 by m by f
  f2 = inst a2 by m  
  f3 = invcmp cmp and (m :: Nat) (forall y . (y :: Nat) * (Le y m) -> y :: C) f f1 : (m :: Nat) * (forall y . (y :: Nat) * (Le y m) -> y :: C)
  f4 = mp f2 by f3
  f5 = ug C . discharge a1 . discharge a2 . ug m . discharge f . f4
qed

theorem succLess. forall n . n :: Nat -> Le n (succ n)
proof
        a = simpCmp inst indNat by iota n . Le n (succ n)
        base = inst sucY by zero
        [ih] : Le x (succ x)
        -- show Le (succ x) (succ (succ x))
        b = byEval (succ x < succ (succ x)) (x < succ x)
        b1 = invcmp cmp ih : Eq (x < succ x) true
        b2 = invcmp chain (succ x < succ (succ x)) (b1 @ b @ nil) : Le (succ x) (succ (succ x))
        b3 = ug x . discharge ih . b2
        r = mp mp a by base by b3
qed

theorem self . forall n . n :: Nat -> Le n n -> Bot
proof
        a = simpCmp inst indNat by iota n . Le n n -> Bot
        [a1] : Le zero zero
        base = byEval false (zero < zero) 
        b = invcmp cmp a1 : Eq (zero < zero) true
        b1 = invcmp chain false (b @ base @ nil) : Eq false true
        b2 = mp boolContra by useSym false true b1
        b3 = discharge a1 . b2
        [ih] : Le x x -> Bot
        -- show Le (succ x) (succ x) -> Bot
        c = byEval (x < x) (succ x < succ x) 
        [c1] : Le (succ x) (succ x)
        c2 = invcmp cmp c1 : Eq (succ x < succ x) true
        c3 = invcmp cmp chain (x < x) ( c2 @ c @ nil) : Le x x
        c4 = mp ih by c3
        c5 = ug x . discharge ih . discharge c1 . c4
        d = mp mp a by b3 by c5
qed

theorem betterSelf . forall n . n :: Nat -> Eq (n < n) false
proof
        a = simpCmp inst indNat by iota n . Eq (n < n) false
        base = byEval (zero < zero) false
        [ih] : Eq (x < x) false
        -- show Le (succ x) (succ x) -> Bot
        c = byEval (succ x < succ x) (x < x)
        c3 = invcmp cmp chain (succ x < succ x) ( ih @ c @ nil) : Eq ((succ x) < (succ x)) false
        c5 = ug x . discharge ih . c3
        d = mp mp a by base by c5
qed

theorem transitivity . forall a b c . a :: Nat -> b :: Nat -> c :: Nat -> Le a b -> Le b c -> Le a c
proof
        f = simpCmp inst weakInd by iota b . forall a c . a :: Nat -> c :: Nat -> Le a b -> Le b c -> Le a c
        [f1] : a :: Nat
        [f3] : Le a zero
        f2 = mp mp inst lessZero by a by f1 by f3
        f4 = invcmp inst inst cmp f2 by a < c by true : Le a c
        f5 = ug a . ug c . discharge f1 . discharge f9 : c :: Nat . discharge f3 . discharge f8 : Le zero c . f4
        [ih] : (y :: Nat) * (forall a . forall c . a :: Nat -> c :: Nat -> Le a y -> Le y c -> Le a c)
        ih1 = smartFirst (y :: Nat) (forall a . forall c . a :: Nat -> c :: Nat -> Le a y -> Le y c -> Le a c) ih 
        ih2 = smartSecond (y :: Nat) (forall a . forall c . a :: Nat -> c :: Nat -> Le a y -> Le y c -> Le a c) ih 
        -- show forall a . forall c . a :: Nat -> c :: Nat -> Le a (succ y) -> Le (succ y) c -> Le a c
        g = simpCmp inst weakInd by iota a . forall c . c :: Nat -> Le a (succ y) -> Le (succ y) c -> Le a c
        -- show forall c . c :: Nat -> Le zero (succ y) -> Le (succ y) c -> Le zero c by IH..
        h = simpCmp inst indNat by iota c . Le zero (succ y) -> Le (succ y) c -> Le zero c
        [h1] : Le (succ y) zero
        h2 = mp inst lessZero by (succ y) by (mp inst surSuc by y by ih1)
        h3 = mp h2 by h1
        h4 = invcmp inst inst cmp h3 by (zero < zero) by true : Le zero zero
        h5 = discharge h6 : Le zero (succ y) . discharge h1 . h4
        [i] : Le zero (succ y) -> Le (succ y) x -> Le zero x
        i1 = discharge i3 : Le zero (succ y) . discharge i2 : Le (succ y) (succ x) . inst sucY by x
        i4 = ug x . discharge i . i1
        i5 = mp mp h by h5 by i4 -- done
        [j] : (y0 :: Nat) * (forall c . c :: Nat -> Le y0 (succ y) -> Le (succ y) c -> Le y0 c)
        -- show forall c . c :: Nat -> Le (succ y0) (succ y) -> Le (succ y) c -> Le (succ y0) c by IH
        j1 = smartFirst (y0 :: Nat) (forall c . c :: Nat -> Le y0 (succ y) -> Le (succ y) c -> Le y0 c) j
        j2 = smartSecond (y0 :: Nat) (forall c . c :: Nat -> Le y0 (succ y) -> Le (succ y) c -> Le y0 c) j
        j3 = simpCmp inst weakInd by iota c . Le (succ y0) (succ y) -> Le (succ y) c -> Le (succ y0) c
        [k] : Le (succ y) zero
        k1 = mp inst lessZero by (succ y) by (mp inst surSuc by y by ih1)
        k2 = mp k1 by k
        k3 = invcmp inst inst cmp k2 by (succ y0) < zero by true : Le (succ y0) zero
        k4 = discharge k5 : Le (succ y0) (succ y) . discharge k . k3
        [l] : (y01 :: Nat) * (Le (succ y0) (succ y) -> Le (succ y) y01 -> Le (succ y0) y01)
        l1 = smartFirst (y01 :: Nat) (Le (succ y0) (succ y) -> Le (succ y) y01 -> Le (succ y0) y01) l
        l2 = smartSecond (y01 :: Nat) (Le (succ y0) (succ y) -> Le (succ y) y01 -> Le (succ y0) y01) l
        -- show Le (succ y0) (succ y) -> Le (succ y) (succ y01) -> Le (succ y0) (succ y01)
        [l3] : Le (succ y0) (succ y)
        [l4] : Le (succ y) (succ y01)
        m = byEval (y0 < y) (succ y0 < succ y)
        m1 = invcmp cmp l3 : Eq (succ y0 < succ y) true
        m2 = invcmp cmp chain (y0 < y) ( m1 @ m @ nil) : Le y0 y
        n = byEval (y < y01) (succ y < succ y01)
        n1 = invcmp cmp l4 : Eq (succ y < succ y01) true
        n2 = invcmp cmp chain (y < y01) ( n1 @ n @ nil) : Le y y01
        n3 = mp mp inst inst ih2 by y0 by y01 by j1 by l1
        n4 = mp mp n3 by m2 by n2 : Le y0 y01
        o = invcmp cmp n4 : Eq (y0 < y01) true
        o1 = byEval (succ y0 < succ y01) (y0 < y01)
        o2 = invcmp cmp chain (succ y0 < succ y01) (o @ o1 @ nil) : Le (succ y0) (succ y01)
        o3 = discharge l3 . discharge l4 . o2
        o4 = ug y01 . discharge l . o3
        o5 = mp mp j3 by k4 by o4
        p = ug y0 . discharge j . o5        
        p1 = mp mp g by i5 by p         
        p2 = inst p1 by m 
        [p3] : m :: Nat
        p4 = inst mp p2 by p3 by c
        [p5] : c :: Nat
        p6 = mp p4 by p5
        p7 = ug m . ug c . discharge p3 . discharge p5 . p6
        q = mp mp f by f5 by ug y . discharge ih . p7
        [q2] : a :: Nat
        [q3] : b :: Nat
        [q4] : c :: Nat
        r1 = inst q by b
        r2 = inst inst mp r1 by q3 by a by c
        r3 = mp mp r2 by q2 by q4
        r4 = ug a . ug b. ug c . discharge q2 . discharge q3 . discharge q4 . r3
        
qed

theorem man . forall m . m :: Nat -> Eq (m - zero) m
proof
        a = simpCmp inst indNat by iota m . Eq (m - zero) m
        a1 = byEval (zero - zero) zero
        [ih] : Eq (x - zero) x
        b = byEval (succ x - zero) (succ x)
        b1 = ug x . discharge ih . b
        b2 = mp mp a by a1 by b1
        
qed

theorem minor . forall n m . n :: Nat -> m :: Nat -> n - m :: Nat
proof
     a = simpCmp inst weakInd by iota n . forall m . m :: Nat -> n - m :: Nat
     b = byEval zero (zero - m )
     b1 =  cmp inst cmp b by iota z . z :: Nat
     b2 = invcmp mp b1 by cmp surZ : zero - m :: Nat
     b3 = ug m . discharge b4 : m :: Nat . b2
     [ih] : (y :: Nat) * (forall m . m :: Nat -> y - m :: Nat)
     ih1 = smartFirst (y :: Nat) (forall m . m :: Nat -> y - m :: Nat) ih
     ih2 = smartSecond (y :: Nat) (forall m . m :: Nat -> y - m :: Nat) ih
     --  to show : forall m . m :: Nat -> (succ y) - m :: Nat)
     c = simpCmp inst weakInd by iota m . succ y - m :: Nat
     c1 = mp (inst man by succ y) by (mp inst surSuc by y by ih1)
     e1 = useSym (succ y - zero) (succ y) c1     
     e2 = mp inst surSuc by y by ih1
     e3 = mp simpCmp inst cmp e1 by iota z . z :: Nat by e2
     [c2] : (y0 :: Nat) * (succ y - y0 :: Nat)
     c3 = smartFirst (y0 :: Nat) (succ y - y0 :: Nat) c2
     c4 = smartSecond (y0 :: Nat) (succ y - y0 :: Nat) c2
     -- show succ y - (succ y0) :: Nat
     c5 = byEval (y - y0) (succ y - succ y0)
     c6 = mp inst ih2 by y0 by c3
     c7 = simpCmp inst cmp c5 by iota z . z :: Nat 
     c8 = mp c7 by c6
     c9 = ug y0 . discharge c2 . c8
     d = mp mp c by e3 by c9
     d1 = ug y . discharge ih . d      
     d2 = mp mp a by b3 by d1     
     [f1] : n :: Nat 
     [f2] : m :: Nat
     f3 = mp inst mp inst d2 by n by f1 by m by f2
     f4 = ug n . ug m . discharge f1 . discharge f2 . f3
qed

theorem substract . forall n x . n :: Nat -> x :: Nat -> Le n (n - x) -> Bot
proof
        a = simpCmp inst weakInd by iota n . forall x. x :: Nat -> Le n (n - x) -> Bot
        [a1] : Le zero (zero - x)
        a3 = simpCmp inst cmp byEval (zero - x) zero by iota z . Le zero z
        a2 = mp a3 by a1 : Le zero zero
        a4 = mp mp (inst self by zero) by surZ by a2
        a5 = ug  x . discharge a6 : x :: Nat . discharge a1 . a4
        [ih] : (y :: Nat) * (forall x . x :: Nat -> Le y (y - x) -> Bot)
        ih1 = invcmp first (y :: Nat) (forall x . x :: Nat -> Le y (y - x) -> Bot) ih : y :: Nat
        ih2 = invcmp second (y :: Nat) (forall x . x :: Nat -> Le y ( y - x) -> Bot) ih : (forall x . x :: Nat -> Le y (y - x) -> Bot)
        -- show forall x . x :: Nat -> Le (succ y) ((succ y) - x) -> Bot
        b = simpCmp inst weakInd by iota x . Le (succ y) ((succ y) - x) -> Bot
        [b1] : Le (succ y) (succ y - zero) 
        b2 = byEval (succ y - zero) (succ y)
        b3 = simpCmp inst cmp b2 by iota z . Le (succ y) z
        b4 = mp b3 by b1
        b5 = inst self by (succ y)
        b6 = mp inst surSuc by y by ih1
        b7 = mp mp b5 by b6 by b4
        b8 = discharge b1 . b7
        [c] : (y0 :: Nat) * (Le (succ y) (succ y - y0) -> Bot)
        c1 = smartFirst (y0 :: Nat) (Le (succ y) (succ y - y0) -> Bot) c
        c2 = smartSecond (y0 :: Nat) (Le (succ y) (succ y - y0) -> Bot) c
        -- show Le (succ y) (succ y - succ y0) -> Bot
        [d] : Le (succ y) (succ y - succ y0)
        d2 = byEval (succ y - succ y0) (y - y0)
        d3 = simpCmp inst cmp d2 by iota z . Le (succ y) z        
        d4 = mp d3 by d -- Le (succ y) ((-) y y0)
        d5 = mp inst succLess by y by ih1 -- Le y (succ y)
        d6 = inst inst inst transitivity by y by (succ y) by (y - y0)
        e1 = mp mp inst inst minor by y by y0 by ih1 by c1
        d7 = mp mp mp mp mp d6 by ih1 by mp (inst surSuc by y) by ih1 by e1 by d5 by d4
        e2 = mp mp inst ih2 by y0 by c1 by d7
        e3 = ug y0 . discharge c . discharge d . e2
        f1 = mp mp b by b8 by e3
        f2 = ug y . discharge ih . f1
        f3 = mp mp a by a5 by f2
        [q1] : n :: Nat
        f4 = ug n . ug x . discharge q1 . inst mp inst f3 by n by q1 by x
qed

-- sub can actually be derived from substract above with transitivity, man, what a waste.
theorem sub. forall n m . n :: Nat -> m :: Nat -> Le zero m -> Le n (succ n - m) -> Bot
proof
--        [a1] : Le zero m
        a = simpCmp inst weakInd by iota m . forall n . n :: Nat -> Le zero m -> Le n (succ n - m) -> Bot
        [b] : Le zero zero
        b1 = invcmp cmp b : Eq (zero < zero) true
        b2 = byEval false (zero < zero)
        b3 = invcmp chain false (b1 @ b2 @ nil) : Eq false true
        b4 = mp boolContra by useSym false true b3
        b5 = ug n . discharge b7 : n :: Nat . discharge b . discharge b6 : Le n ((succ n) - zero) . b4
        [ih'] : (x :: Nat) * (forall n . n :: Nat -> Le zero x -> Le n ((succ n) - x) -> Bot)
        ih = smartSecond (x :: Nat) (forall n . n :: Nat -> Le zero x -> Le n ((succ n) - x) -> Bot) ih'
        nat = smartFirst (x :: Nat) (forall n . n :: Nat -> Le zero x -> Le n ((succ n) - x) -> Bot) ih'
        -- show forall n . n :: Nat -> Le zero (succ x) -> Le n ((succ n) - (succ x)) -> Bot
        c = simpCmp inst weakInd by iota n . Le zero (succ x) -> Le n ((succ n) - (succ x)) -> Bot         
        [c1] : Le zero (succ zero - succ x)
        c2 = simpCmp inst cmp byEval (succ zero - succ x) zero by iota z . Eq (zero < z) true 
        c3 = mp c2 by invcmp cmp c1 from Eq (zero < succ zero - succ x) true
        c4 = byEval false (zero < zero)
        c5 = invcmp chain false (c3 @ c4 @ nil) : Eq false true
        c6 = mp boolContra by useSym false true c5
        c7 = discharge c8 : Le zero (succ x) . discharge c1 . c6
        [ih2] : (y :: Nat) * (Le zero (succ x) -> Le y (succ y - succ x) -> Bot)
        -- show Le zero (succ x) -> Le (succ y) ((succ (succ y)) - (succ x)) -> Bot
        d1 = smartFirst (y :: Nat) (Le zero (succ x) -> Le y (succ y - succ x) -> Bot) ih2
        d2 = smartSecond (y :: Nat) (Le zero (succ x) -> Le y (succ y - succ x) -> Bot) ih2
        [d3] : Le zero (succ x)
        [d4] : Le (succ y) ((succ (succ y)) - (succ x))
        d = byEval (succ (succ y) - succ x) (succ y - x)
        d5 = mp simpCmp inst cmp d by iota z . Le (succ y) z by d4 -- Le (succ y) ((-) (succ y) x)
        d6 = mp mp inst inst substract by succ y by x by mp inst surSuc by y by d1 by nat
        d7 = mp d6 by d5
        d8 = ug y . discharge ih2 . discharge d3 . discharge d4 . d7
        e1 = mp mp c by c7 by d8
        e2 = ug x . discharge ih' . e1        
        e3 = mp mp a by b5 by e2        
        [f1] : n :: Nat
        [f2] : m :: Nat
        f3 = ug n . ug m . discharge f1 . discharge f2 . mp inst mp inst e3 by m by f2 by n by f1
qed

tactic red t1 = 
   [c] : t1 :: Q
   c1 = beta c 
   c3 = ug Q . discharge c . c1

theorem zeroDiv . forall m . m :: Nat -> Le zero m -> Eq (div zero m) zero 
proof
        a = simpCmp inst weakInd by iota m . Le zero m -> Eq (div zero m) zero 
        [a1] : Le zero zero
        a2 = mp mp inst lessZero by zero by surZ by a1
        a3 = invcmp inst inst cmp a2 by (div zero zero) by zero : Eq (div zero zero) zero
        a4 = discharge a1 . a3
        [ih] : (y :: Nat) * (Le zero y -> Eq (div zero y) zero)
        -- show Le zero (succ y) -> Eq (div zero (succ y)) zero
        b =  byEval (div zero (succ y)) zero
        b1 = ug y . discharge ih . discharge b6 : Le zero (succ y) . b
        b2 = mp mp a by a4 by b1         

qed

theorem totalBool . forall b . b :: Bool -> Eq b true <+> Eq b false
proof
        a = simpCmp inst indBool by iota b . Eq b true <+> Eq b false
        a1 = byEval true true
        a2 = invcmp cmp inj1 (Eq true true) (Eq true false) a1 : (Eq true true) <+> (Eq true false)
        b1 = byEval false false
        b2 = invcmp cmp inj2 (Eq false true) (Eq false false) b1 :  (Eq false true) <+> (Eq false false)
        b3 = mp mp a by a2 by b2
qed

tactic convert p A = invcmp cmp p from A
theorem surTrue . true :: Bool
proof
        a = ug C . discharge a1 : true :: C . discharge a2 : false :: C . a1
        b = convert a (true :: Bool)
qed

theorem surFalse . false :: Bool
proof
        a = ug C . discharge a1 : true :: C . discharge a2 : false :: C . a2
        b = convert a (false :: Bool)
qed

-- p1 : C[x] , p2 : x = y, S = iota x . C[x]
tactic congByEq p1 p2 S = 
        a = simpCmp inst cmp p2 by S
        a1 = mp a by p1

tactic instInd p S = simpCmp inst p by S         

theorem totalLess . forall n m . n :: Nat -> m :: Nat -> n < m :: Bool
proof
        a = simpCmp inst indNat by iota n . forall m . m :: Nat -> n < m :: Bool
        a1 = simpCmp inst indNat by iota m . zero < m :: Bool
        a2 = byEval false (zero < zero)
        a3 = congByEq surFalse a2 (iota z . z :: Bool)
        b1 = byEval true (zero < succ x)
        b2 = congByEq surTrue b1 (iota z . z :: Bool)
        b3 = ug x . discharge c1 : zero < x :: Bool . b2
        c2 = mp mp a1 by a3 by b3
        [ih] : forall m . m :: Nat -> x < m :: Bool
        -- show forall m . m :: Nat -> (succ x) < m :: Bool
        a4 = instInd weakInd (iota m . (succ x) < m :: Bool)
        d = byEval false (succ x < zero)
        d1 = congByEq surFalse d (iota z . z :: Bool)
        [ih2] : (y :: Nat) * ( succ x < y :: Bool)
        ih3 = smartFirst (y :: Nat) ( succ x < y :: Bool) ih2
        d2 = mp inst ih by y by ih3
        d3 = byEval (x < y) (succ x < succ y)
        d4 = congByEq d2 d3 (iota z . z :: Bool)
        d5 = ug y . discharge ih2 . d4
        d6 = mp mp a4 by d1 by d5
        e = ug x . discharge ih . d6        
        e1 = mp mp a by c2 by e         
        [f] : n :: Nat
        f1 = ug n . ug m . discharge f . inst mp inst e1 by n by f by m
qed

-- much better refl.
tactic refl t = invcmp ug E . discharge a : t :: E . a from Eq t t

theorem suucc . forall x . x :: Nat -> Le (succ x) x -> Bot 
proof
        a = instInd indNat (iota x . Le (succ x) x -> Bot)
        a1 = mp inst lessZero by (succ zero) by mp inst surSuc by zero by surZ
        [b] : Le (succ x) x -> Bot
        [b1] : Le (succ (succ x)) (succ x)
        b2 = convert b1 (Eq (succ (succ x) < succ x) true)
        b3 = byEval (succ x < x) (succ (succ x) < succ x)
        b4 = invcmp chain (succ x < x) (b2 @ b3 @ nil) from Le (succ x) x
        b5 = ug x . discharge b . discharge b1 . mp b by b4
        c = mp mp a by a1 by b5
qed

theorem notEq . Eq (succ zero) zero -> Bot
proof
        [a] : Eq (succ zero) zero
        b = smartCong (\ n . n x (\ u . y)) (succ zero) zero a y x
        c = convert (ug y . ug x . b) Bot
        r = discharge a . c
qed

theorem suuccEqq . forall x . x :: Nat -> Eq (succ x) x -> Bot 
proof
        a = instInd indNat (iota x . Eq (succ x) x -> Bot)
        a1 = notEq
        [b] : Eq (succ x) x -> Bot
        [b1] : Eq (succ (succ x)) (succ x)
        b2 = smartCong pred (succ (succ x)) (succ x) b1 (\ z s . s x) x : Eq (\ z s . s x) x
        b21 = byEval (succ x) (\ z s . s x)
        b22 = invcmp chain (succ x) ( b2 @ b21 @ nil) : Eq (succ x) x
        b3 = ug x . discharge b . discharge b1 . mp b by b22
        r = mp mp a by a1 by b3
qed

theorem inverse . forall x m . x :: Nat -> m :: Nat -> Le zero m -> Le m x -> Eq x (x - m) -> Bot
proof
        a = instInd weakInd (iota x . forall m . m :: Nat -> Le zero m -> Le m x -> Eq x (x - m) -> Bot)
        [b3] : m :: Nat
        [b] : Le m zero
        b1 = mp mp inst lessZero by m by b3 by b
        b2 = ug m . discharge b3 . discharge b4 : Le zero m . discharge b  . discharge b5 : Eq zero (zero - m) . b1
        [ih] : (y :: Nat) * (forall m . m :: Nat -> Le zero m -> Le m y -> Eq y (y - m) -> Bot)
-- show forall m . m :: Nat -> Le zero m -> Le m (succ y) -> Eq (succ y) ((succ y) - m) -> Bot
        ih1 = smartFirst (y :: Nat) (forall m . m :: Nat -> Le zero m -> Le m y -> Eq y (y - m) -> Bot) ih
        ih2 = smartSecond (y :: Nat) (forall m . m :: Nat -> Le zero m -> Le m y -> Eq y (y - m) -> Bot) ih
        [c] : m :: Nat
        [c1] : Le zero m
        [c2] : Le m (succ y)
        [c3] : Eq (succ y) (succ y - m)
        c4 = mp mp mp inst inst sub by y by m by ih1 by c by c1
        c5 = mp inst succLess by y by ih1
        c6 = congByEq c5 c3 (iota z . Le y z)
        c7 = mp c4 by c6
        c8 = ug m . discharge c . discharge c1 . discharge c2 . discharge c3 . c7
        d = ug y . discharge ih . c8
        r = mp mp a by b2 by d        
        [r1] : x :: Nat
        r2 = ug x . ug m . discharge r1 . inst mp inst r by x by r1 by m
qed

theorem sub2 . forall x m . x :: Nat -> m :: Nat -> Le zero m -> Le m x -> Le (x - m) x 
proof
        [a1] : x :: Nat
        [a2] : m :: Nat
        [a0] : Le zero m
        [a01] : Le m x
        a = mp mp inst inst substract by x by m by a1 by a2
        a3 = mp mp inst inst tri by x by x - m by a1 by (mp mp inst inst minor by x by m by a1 by a2)
        [b] : Le x (x - m)
        b1 = mp mp inst inst substract by x by m by a1 by a2
        b2 = mp b1 by b
        b3 = discharge b . b2
      --  [c] : Eq x (x - m)
        c = mp mp mp mp inst inst inverse by x by m by a1 by a2 by a0 by a01
        c1 = sumElim (Le x (x - m)) (Eq x (x - m)) Bot b3 c
        [d] : (Le x (x - m)) <+> (Eq x (x - m))
        d1 = mp c1 by d
        d2 = discharge d . convert (inst inst cmp d1 by (x - m < x) by true) (Le (x - m) x)
        d3 = id (Le (x - m) x)
        d4 = sumElim ((Le x (x - m)) <+> (Eq x (x - m))) (Le (x - m) x) (Le (x - m) x) d2 d3
        d5 = mp d4 by a3 
        e = ug x . ug m . discharge a1 . discharge a2 . discharge a0 . discharge a01 . d5       
qed

theorem subRefl . forall m . m :: Nat -> Eq (m - m) zero
proof
        a = instInd indNat (iota m . Eq (m - m) zero)
        a1 = byEval (zero - zero) zero
        [ih] : Eq (x - x) zero
        b = byEval (succ x - succ x) (x - x)
        b2 = invcmp chain (succ x - succ x) (ih @ b @ nil) : Eq (succ x - succ x) zero
        b3 = ug x . discharge ih . b2
        b4 = mp mp a by a1 by b3
qed

theorem subEq . forall x m . x :: Nat -> m :: Nat -> Eq x m -> Eq (x - m) zero
proof
        [a0] : m :: Nat
        [a] : Eq x m
        a1 = betterCong (\ y . y - m) x m a (x - m) (m - m)
        a2 = mp inst subRefl by m by a0
        a3 = invcmp chain (x - m) (a2 @ a1 @ nil) : Eq (x - m ) zero
        a4 = ug x . ug m . discharge a00 : x :: Nat . discharge a0 . discharge a . a3
qed

theorem divZero . forall m . Le zero m -> Eq (div zero m) zero
proof
        [a0] : Le zero m
        a = byEval (div zero m) ((zero < m) zero (succ (div (zero - m) m)))
        a1 = convert a0 (Eq (zero < m) true)
        a2 = let nu = ((zero < m) zero (succ (div (zero - m) m))) in
                 congByEq (refl nu ) a1 (iota z . Eq nu (z zero (succ (div (zero - m) m))))
        -- Eq ((zero < m) zero (succ (div (zero - m) m))) (true zero (succ (div ((-) zero m) m)))
        a3 = byEval (true zero (succ (div (zero - m) m))) zero
        a4 = invcmp chain (div zero m) ( a3 @ a2 @ a @ nil) : Eq (div zero m) zero
        a5 = ug m . discharge a0 . a4
        
qed

theorem noLess . forall x m . x :: Nat -> m :: Nat -> Eq x m -> Eq (x < m) false
proof
        [a] : x :: Nat
        [a0] : m :: Nat
        [a1] : Eq x m
        a11 = useSym x m a1
        b = mp inst betterSelf by m by a0
        b1 = congByEq b a11 (iota z . Eq (z < m) false)
        b2 = ug x . ug m . discharge a . discharge a0. discharge a1 . b1
qed

theorem divOne . forall x m . x :: Nat -> m :: Nat -> Le zero m -> Eq x m 
                        -> Eq (div x m) (succ zero)
proof
        [a0] : x :: Nat
        [a1] : m :: Nat
        [a2] : Le zero m
        [a3] : Eq x m
        b = mp mp mp inst inst noLess by x by m by a0 by a1 by a3         
        c1 = byEval (div x m) ((x < m) zero (succ (div (x - m) m)))
        c2 = congByEq (refl ((x < m) zero (succ (div (x - m) m)))) b (iota z . Eq ((x < m) zero (succ (div (x - m) m))) (z zero (succ (div (x - m) m))))
        c3 = byEval (false zero (succ (div (x - m) m))) (succ (div (x - m) m)) 
        c4 = invcmp chain (div x m) (c3 @ c2 @ c1 @ nil) : Eq (div x m) (succ (div (x - m) m)) 
        d = mp mp mp inst inst subEq by x by m by a0 by a1 by a3
        d1 = congByEq c4 d (iota z . Eq (div x m) (succ (div z m)))
        d2 = mp inst divZero by m by a2
        d3 = congByEq d1 d2 (iota z . Eq (div x m) (succ z))
        d4 = ug x . ug m . discharge a0 . discharge a1 . discharge a2 . discharge a3 . d3        
qed

theorem mamm . forall x m . x :: Nat -> m :: Nat -> Eq (x < m) false -> (Le m x) <+> (Eq m x) 
proof
        [a0] : x :: Nat
        [a1] : m :: Nat
        [a2] : Eq (x < m) false
        a = mp mp inst inst tri by m by x by a1 by a0
        [b] : Le x m
        b1 = convert b (Eq (x < m) true)
        b2 = useSym (x < m) true b1
        b3 = invcmp chain true (a2 @ b2 @ nil) : Eq true false
        b4 = mp boolContra by b3
        b5 = invcmp inst inst cmp b4 by m by x : Eq m x
        b6 = convert (inj2 (Le m x) (Eq m x) b5) ((Le m x) <+> (Eq m x))
        b7 = discharge b . b6
        b8 = id ((Le m x) <+> (Eq m x))
        b9 = sumElim ((Le m x) <+> (Eq m x)) (Le x m) ((Le m x) <+> (Eq m x)) b8 b7
        c = mp b9 by a
        c1 = ug x . ug m . discharge a0 . discharge a1 . discharge a2 . c        
qed

theorem divTotal . forall x m . x :: Nat -> m :: Nat -> Le zero m -> div x m :: Nat
proof
          [a00] : u :: Nat
          [a0] : m :: Nat
          a = simpCmp inst strongInd by iota x . Le zero m -> div x m :: Nat
          [a3] : Le zero m
          a2 = useSym (div zero m) zero (mp mp inst zeroDiv by m by a0 by a3)
          a4 = mp simpCmp inst cmp a2 by iota z . z :: Nat by surZ
          a5 = discharge a3 . a4
          [ih] : (x :: Nat) * (forall y . (y :: Nat) * (Le y x) -> Le zero m -> div y m :: Nat)
          ih1 = smartFirst (x :: Nat) (forall y . (y :: Nat) * (Le y x) -> Le zero m -> div y m :: Nat) ih
          ih2 = smartSecond (x :: Nat) (forall y . (y :: Nat) * (Le y x) -> Le zero m -> div y m :: Nat) ih
          -- show Le zero m -> div x m :: Nat
          [b] : Le zero m           
          b1 = mp mp inst inst totalLess by x by m by ih1 by a0 : x < m :: Bool
          b2 = mp inst totalBool by (x < m) by b1
          [c] : Eq (x < m) true
          c1 = byEval (div x m) ((x < m) zero (succ (div (x - m) m)))
          c2 = congByEq (refl ((x < m) zero (succ (div (x - m) m)))) c (iota z . Eq ((x < m) zero (succ (div (x - m) m))) (z zero (succ (div (x - m) m))))
          c3 = byEval (true zero (succ (div (x - m) m))) zero
          c4 = invcmp chain (div x m) ( c3 @ c2 @ c1 @ nil) : Eq (div x m) zero
          c5 = congByEq surZ (useSym (div x m) zero c4) (iota z . z :: Nat)
          c7 = discharge c . c5
          [d] : Eq (x < m) false
          d1 = congByEq (refl ((x < m) zero (succ (div (x - m) m)))) d (iota z . Eq ((x < m) zero (succ (div (x - m) m))) (z zero (succ (div (x - m) m))))
          d2 = byEval (false zero (succ (div ( x - m) m))) (succ (div ( x - m) m))
          d3 = invcmp chain (div x m) ( d2 @ d1 @ c1 @ nil) : Eq (div x m) (succ (div ( x - m) m))
          d30 = useSym (div x m) (succ (div ( x - m) m)) d3
          d4 = inst ih2 by (x - m)
          d5 = mp mp inst inst minor by x by m by ih1 by a0
          d6 = mp mp mp inst inst sub2 by x by m by ih1 by a0 by b          
          [e] : Le m x
          d7 = mp d6 by e        
          d8 = convert (and ( x -  m :: Nat) (Le (x - m) x) d5 d7) (( x -  m :: Nat) * (Le (x - m) x))
          d9 = mp mp d4 by d8 by b
          d10 = mp inst surSuc by (div (x - m) m) by d9
          d11 = congByEq d10 d30 (iota z . z :: Nat)
          d12 = discharge e . d11
          [e1] : Eq m x
          e11 = useSym m x e1
          e2 = mp mp mp mp inst inst divOne by x by m by ih1 by a0 by b by e11
          e3 = mp (inst surSuc by zero) by surZ
          e4 = congByEq e3 (useSym (div x m) (succ zero) e2) (iota z . z :: Nat)
          e5 = discharge e1 . e4
          e6 = sumElim (Le m x) (Eq m x) (div x m :: Nat) d12 e5
          f = mp mp mp inst inst mamm by x by m by ih1 by a0 by d
          f1 = mp e6 by f
          f2 = discharge d . f1
          f3 = sumElim (Eq (x < m) true) (Eq (x < m) false) (div x m :: Nat) c7 f2
          g = mp f3 by b2
          g1 = ug x . discharge ih . discharge b . g
          g2 = mp mp a by a5 by g1
          g3 = ug u . ug m . discharge a00 . discharge a0 . mp inst g2 by u by a00

qed

theorem anotherContra . forall n m . n :: Nat -> m :: Nat -> Le n m -> Eq n m -> Bot
proof
        [a0] : n :: Nat
        [a1] : m :: Nat
        [a] : Le n m
        [b] : Eq n m
        c = congByEq a b (iota z . Le z m)
        c1 = mp mp (inst self by m) by a1 by c
        r = ug n . ug m . discharge a0 . discharge a1 . discharge a . discharge b . c1
qed

theorem division. forall n m . n :: Nat -> m :: Nat -> Le zero m -> Le n (div n m) -> Bot
proof
        [i] : n :: Nat
        [a0] : m :: Nat
        a = simpCmp inst strongInd by iota n . Le zero m -> Le n (div n m) -> Bot
        [a3] : Le zero m
        [a1] : Le zero (div zero m)
        a2 = mp mp inst zeroDiv by m by a0 by a3
        a4 = simpCmp inst cmp a2 by iota z . Le zero z
        a5 = mp a4 by a1
        a6 = mp mp inst lessZero by zero by surZ by a5
        a7 = discharge a3 . discharge a1 . a6
        [ih] : (x :: Nat) * (forall y . (y :: Nat) * (Le y x) -> Le zero m -> Le y (div y m) -> Bot)
        ih1 = smartFirst (x :: Nat) (forall y . (y :: Nat) * (Le y x) -> Le zero m -> Le y (div y m) -> Bot) ih
        ih2 = smartSecond (x :: Nat) (forall y . (y :: Nat) * (Le y x) -> Le zero m -> Le y (div y m) -> Bot) ih
        -- show Le zero m -> Le x (div x m) -> Bot
        [b] : Le zero m
        [b0] : Le x (div x m)
        b1 = mp mp inst inst totalLess by x by m by ih1 by a0 : x < m :: Bool
        b2 = mp inst totalBool by (x < m) by b1
        [c] : Eq (x < m) true
        c1 = byEval (div x m) ((x < m) zero (succ (div (x - m) m)))
        c2 = congByEq (refl ((x < m) zero (succ (div (x - m) m)))) c (iota z . Eq ((x < m) zero (succ (div (x - m) m))) (z zero (succ (div (x - m) m))))
        c3 = byEval (true zero (succ (div (x - m) m))) zero
        c4 = invcmp chain (div x m) ( c3 @ c2 @ c1 @ nil) : Eq (div x m) zero
        c5 = congByEq b0 c4 (iota z . Le x z)
        c6 = mp mp inst lessZero by x by ih1 by c5
        c7 = discharge c . c6
--        c5 = discharge c . c4 : Eq (x < m) true -> Eq (div x m) zero
        [d] : Eq (x < m) false
        d1 = congByEq (refl ((x < m) zero (succ (div (x - m) m)))) d (iota z . Eq ((x < m) zero (succ (div (x - m) m))) (z zero (succ (div (x - m) m))))
        d2 = byEval (false zero (succ (div ( x - m) m))) (succ (div ( x - m) m))
        d3 = invcmp chain (div x m) ( d2 @ d1 @ c1 @ nil) : Eq (div x m) (succ (div ( x - m) m))
        d4 = inst ih2 by (x - m)
        d5 = mp mp inst inst minor by x by m by ih1 by a0
        d6 = mp mp mp inst inst sub2 by x by m by ih1 by a0 by b
        [e] : Le m x
        d7 = mp d6 by e        
        d8 = convert (and ( x -  m :: Nat) (Le (x - m) x) d5 d7) (( x -  m :: Nat) * (Le (x - m) x))
        d9 = mp mp d4 by d8 by b
        d11 = mp mp mp inst inst divTotal by x by m by ih1 by a0 by b
        d10 = mp mp mp mp mp inst inst inst transitivity by (x - m) by x by (div x m) by d5 by ih1 by d11 by d7 by b0
        e00 = congByEq d10 d3 (iota z . Le (x - m) z)
        d12 = mp mp mp inst inst divTotal by (x - m) by m by d5 by a0 by b
        e1 = mp mp inst inst less by (x - m) by (div (x - m) m) by d5 by d12
        e2 = mp e1 by e00
        [e3] : Eq (x - m) (div ( x - m) m)
        e4 = congByEq d7 e3 (iota z . Le z x) 
        e41 = congByEq b0 d3 (iota z . Le x z)
        e40 = convert (and (Le (div (x - m) m) x) (Le x (succ (div ( x - m) m))) e4 e41) ((Le (div (x - m) m) x) * (Le x (succ (div ( x - m) m))))
        e5 = mp mp inst inst discrete by x by (div (x - m) m) by ih1 by d12 
        f = discharge e3 . mp e5 by e40
        f1 = sumElim (Le ( x - m) (div ( x - m) m)) (Eq ( x - m) (div ( x - m) m)) Bot d9 f
        f2 = discharge e . mp f1 by e2
        [g] : Eq m x        
        g1 = mp mp mp mp inst inst divOne by x by m by ih1 by a0 by b by (useSym m x g)        
        g2 = congByEq b g (iota z . Le zero z )
        g3 = congByEq b0 g1 (iota z . Le x z)
        g4 = mp mp inst inst discrete by x by zero by ih1 by surZ
        g5 = convert (and (Le zero x) (Le x (succ zero)) g2 g3) ((Le zero x) * (Le x (succ zero)))
        g6 = mp g4 by g5
        g7 = discharge g . g6
        h0 = sumElim (Le m x) (Eq m x) Bot f2 g7
        h = mp mp mp inst inst mamm by x by m by ih1 by a0 by d
        h1 = discharge d . mp h0 by h
        h2 = sumElim (Eq (x < m) true) (Eq (x < m) false) Bot c7 h1        
        h3 = mp h2 by b2
        h4 = discharge b . discharge b0 . h3
        h5 = ug x . discharge ih . h4
        h6 = mp mp a by a7 by h5
        h7 = ug n . ug m . discharge i . discharge a0 . mp inst h6 by n by i
qed

theorem divi. forall n m . n :: Nat -> m :: Nat -> Le zero m -> 
                                       Le (div n m) n <+> Eq (div n m) n
proof
        [a1] : n :: Nat
        [a2] : m :: Nat
        [a3] : Le zero m
        a = id (Le (div n m) n <+> Eq (div n m) n)
        [b1] : Le n (div n m)
        b = mp mp mp mp inst inst division by n by m by a1 by a2 by a3 by b1
        b2 = invcmp inst inst cmp b by (div n m) by n : Eq (div n m) n
        b3 = convert (inj2 (Le (div n m) n) (Eq (div n m) n) b2) ((Le (div n m) n <+> Eq (div n m) n))  
        b4 = discharge b1 . b3
        b5 = sumElim (Le (div n m) n <+> Eq (div n m) n) (Le n (div n m)) (Le (div n m) n <+> Eq (div n m) n) a b4
        c1 = mp mp mp inst inst divTotal by n by m by a1 by a2 by a3
        c = mp mp inst inst tri by (div n m) by n by c1 by a1     
        c2 = mp b5 by c
        r = ug n . ug m . discharge a1 . discharge a2 . discharge a3 . c2

qed