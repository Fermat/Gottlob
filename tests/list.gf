module list where

prog infixl 9 ++
proof infixl 9 ++

Eq a b = forall C . a :: C -> b :: C

data List U where
  nil :: List U
  cons :: U -> List U -> List U
  deriving Ind
  
(++) nil l = l
(++) (cons u l') l = cons u (l' ++ l)

map f nil = nil
map f (cons x xs) = cons (f x) (map f xs)

foldr f a nil = a
foldr f a (cons x xs) = f x (foldr f a xs)


tactic cmpinst p s = cmp inst p by s 
tactic id F =  discharge a : F . a

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

-- t1 -beta-> t1' then red t1 : forall Q. t1::Q -> t1'::Q
tactic red t1 = 
   [c] : t1 :: Q
   c1 = beta c 
   c3 = ug Q . discharge c . c1

-- t1 -beta-> t1' and p: Eq t1' t2
-- syl t1 p : forall Q. t1 :: Q -> t2 :: Q (or Eq t1 t2)
tactic syl t1 p =    
   [c] : t1 :: Q
   c3 = inst (red t1) by Q
   c4 = inst p by Q
   c5 = mp c4 by (mp c3 by c) 
   c6 = ug Q. discharge c . c5

-- This is beyond awesome!!!
-- take in a list of equality proofs and chains them together.
tactic chain t ls = 
       ug Q. discharge a : t :: Q . 
          let insts = map (\ x . inst (cmp x) by Q) ls
              in foldr (\ x y . mp x by y) a insts
           
tactic byEval t1 t2 =   
   [c] : t1 :: Q
   c1 = invbeta beta c : t2 :: Q
   c3 = ug Q . discharge c . c1
   c5 = invcmp c3 : Eq t1 t2

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

tactic useCong f a b p = mp (inst inst inst cong by f by a by b) by p

theorem test. Eq a b
proof
   [a1] : forall C . a :: C -> b :: C
   [a2] : forall D . b :: D -> c :: D
   e = invcmp (chain a (cons a2 (cons a1 nil))) : Eq a c
qed

theorem assoc. forall l1 l2 l3 U . l1 :: List U -> Eq (l1 ++ l2 ++ l3) (l1 ++ (l2 ++ l3))
proof
        ind = let p = iota U z . Eq (z ++ l2 ++ l3) (z ++ (l2 ++ l3))
              in simpCmp inst (inst indList by U) by p
        b = byEval (nil ++ l2 ++ l3) (nil ++ (l2 ++ l3)) 
        [a4] : x :: U
        [ih] : Eq (x0 ++ l2 ++ l3) ( x0 ++ (l2 ++ l3))
        c1 = let f = cons x 
                 g1 = x0 ++ l2 ++ l3
                 g2 = x0 ++ (l2 ++ l3) in
                 useCong f g1 g2 ih : Eq (cons x (x0 ++ l2 ++ l3)) (cons x (x0 ++ (l2 ++ l3)))
        p1 = byEval (cons x x0 ++ l2 ++ l3) (cons x (x0 ++ l2 ++ l3))
        c2 = byEval (cons x (x0 ++ (l2 ++ l3))) (cons x x0 ++ (l2 ++ l3))
        c4 = chain (cons x x0 ++ l2 ++ l3) (cons c2 (cons c1 (cons p1 nil)))
        c5 = invcmp c4 : Eq (cons x x0 ++ l2 ++ l3) (cons x x0 ++ (l2 ++ l3))
        d = ug x . discharge a4. ug x0. discharge ih . c5 
        d1 = mp mp ind by b by d 
        d2 = inst d1 by l1
        [a1] : l1 :: List U
        d3 = mp d2 by a1 
        d4 = ug l1 . ug l2. ug l3 . ug U. discharge a1 . d3 
qed


{-
theorem assoc. forall l1 l2 l3 U . l1 :: List U -> Eq (l1 ++ l2 ++ l3) (l1 ++ (l2 ++ l3))
proof
        ind = let p = iota U z . Eq (z ++ l2 ++ l3) (z ++ (l2 ++ l3))
              in simpCmp inst (inst indList by U) by p
        b = byEval (nil ++ l2 ++ l3) (nil ++ (l2 ++ l3)) 
        [a4] : x :: U
        [ih] : Eq (x0 ++ l2 ++ l3) ( x0 ++ (l2 ++ l3))
        c1 = let f = cons x 
                 g1 = x0 ++ l2 ++ l3
                 g2 = x0 ++ (l2 ++ l3) in
                 useCong f g1 g2 ih : Eq (cons x (x0 ++ l2 ++ l3)) (cons x (x0 ++ (l2 ++ l3)))
        p1 = byEval (cons x x0 ++ l2 ++ l3) (cons x (x0 ++ l2 ++ l3))
        c2 = byEval (cons x (x0 ++ (l2 ++ l3))) (cons x x0 ++ (l2 ++ l3))
        c3 = useTrans (cons x x0 ++ l2 ++ l3) (cons x (x0 ++ l2 ++ l3)) (cons x (x0 ++ (l2 ++ l3))) p1 c1 
        c4 = useTrans (cons x x0 ++ l2 ++ l3) (cons x (x0 ++ (l2 ++ l3))) (cons x x0 ++ (l2 ++ l3)) c3 c2
        d = ug x . discharge a4. ug x0. discharge ih . c4 
        d1 = mp mp ind by b by d 
        d2 = inst d1 by l1
        [a1] : l1 :: List U
        d3 = mp d2 by a1 
        d4 = ug l1 . ug l2. ug l3 . ug U. discharge a1 . d3 
qed

-}









--        e = byEval (cons x x0 ++ l2 ++ l3) (cons x x0 ++ (l2 ++ l3))         
        -- c1 = smartCong (\ z ni con . con x z ) (x0 ++ l2 ++ l3) (x0 ++ (l2 ++ l3)) ih 
        --                   (\ ni con . con x (x0 ++ l2 ++ l3)) 
        --                    (\ ni con . con x (x0 ++ (l2 ++ l3))) 




