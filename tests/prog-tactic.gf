module nat where
proof infixr 9 $
prog infixr 9 !

(!) x y = x y
tactic ($) x y = x y

Eq a b = forall C . a :: C -> b :: C
ExEq f g = forall a . Eq (f a) (g a)
Bot = forall a b . Eq a b
Emp = forall a C . a :: C 
-- E = (g x :: C)
data Nat where
  z :: Nat
  s :: Nat -> Nat 

add n m = 
  case n of
     z -> m 
     s n'-> s ! add n' m
     
gf state a = case a of
           z -> state
           s a' -> let f = f (plus1 state)
                       state = plus1 state in
                     f a'
--
tactic app n p =  n (iota q . Eq (f a) (f q)) $ add n z
tactic cmpinst p s = cmp inst p by s 
tactic test p s = s p $ p2 p3
tactic test1 p s = ($) (s p) p2 p3
-- ( f a :: C)
-- (iota q . Eq (f a) (f q)) p 
tactic iter n p t = case n of 
                      z -> inst p by t
                      s a' -> iter a' p t

tactic smartInst p s A = invcmp (cmp inst p by s) from A
tactic id F =  discharge a : F . a     
tactic byEval t1 t2 =   
   [c] : t1 :: Q
   c1 = invbeta beta c : (t2 :: Q)
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


