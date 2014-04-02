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


-- theorem less. forall y . y :: Nat -> Le y zero -> Bot
-- proof


-- qed
-- theorem less . forall y n . y :: Nat -> n :: Nat -> Le y (succ n) -> Le y n <+> Eq y n
-- proof
--     a = simpCmp inst indNat by (iota z . forall n . n :: Nat -> Le z (succ n) -> Le z n <+> Eq z n)
-- qed


theorem strongInd . forall C . zero :: C -> 
                           (forall x. x :: Nat * (forall y .  y :: Nat * Le y x -> y :: C) 
                               -> x :: C) -> forall m . m :: Nat -> m :: C
proof
  [a1] : zero :: C
  [a2] : forall x. x :: Nat * (forall y .  y :: Nat * Le y x -> y :: C) -> x :: C
  b = simpCmp inst weakInd by (iota z . forall y .  y :: Nat * Le y z -> y :: C)

qed