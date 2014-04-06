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

tactic and U V p1 p2 = ug Y . discharge x : U -> V -> Y . mp (mp x by p1) by p2
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
     c = simpCmp inst weakInd by iota m . y - m :: Nat
     c1 = byEval 
     
     
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
        -- show Le (succ y) (succ y - succ y0) -> Bot
        [d] : Le (succ y) (succ y - succ y0)
        d2 = byEval (succ y - succ y0) (y - y0)
        d3 = simpCmp inst cmp d2 by iota z . Le (succ y) z        
        d4 = mp d3 by d
        d5 = mp inst succLess by y by ih1
        d6 = inst inst inst transitivity by y by (succ y) by (y - y0)
        d7 = mp mp d6 by ih1 by mp (inst surSuc by y) by ih1

qed


theorem sub. forall n m . n :: Nat -> m :: Nat -> Le zero m -> Le n (succ n - m) -> Bot
proof
--        [a1] : Le zero m
        a = simpCmp inst indNat by iota m . forall n . n :: Nat -> Le zero m -> Le n (succ n - m) -> Bot
        [b] : Le zero zero
        b1 = invcmp cmp b : Eq (zero < zero) true
        b2 = byEval false (zero < zero)
        b3 = invcmp chain false (b1 @ b2 @ nil) : Eq false true
        b4 = mp boolContra by useSym false true b3
        b5 = ug n . discharge b7 : n :: Nat . discharge b . discharge b6 : Le n ((succ n) - zero) . b4
        [ih] : forall n . n :: Nat -> Le zero x -> Le n ((succ n) - x) -> Bot
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
        
        
qed
