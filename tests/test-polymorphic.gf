module poly where

data Nat where
  z :: Nat
  s :: Nat -> Nat

data List U where
  nil :: List U
  cons :: U -> List U -> List U

data Pair U V where
  times :: U -> V -> Pair U V
  deriving Ind


-- zip :: List U -> List V -> List (Pair U V)

-- zip nil nil = nil
-- zip (cons a t) (cons b t') = zip a b
c = id
id = \ x . x
exp = let x = id in x
bb = \ x y z . x z (y z)
bb1 = \ x y . x
cc = bb bb1 bb1
aa = let ss = \ x y z . x z (y z)
         kk = \ x y . x
        in ss kk kk




zip1 b e = case b of
              nil -> case e of
                      nil -> nil
              cons a t -> case e of
                            cons b t' -> zip1 t t'

zip2 b e = case b of
              nil -> case e of
                      nil -> nil
              cons a t -> case e of
                            cons q t' -> zip2 t t'
zip3 nil nil = nil
zip3 (cons a t) (cons q t') = zip3 t t'
                           --(zip a b)
--cons (times a b) 
-- zip (cons a t) nil = nil
-- zip nil (cons a t) = nil

-- append :: List U -> List U -> List U
-- append nil l = l
-- append (cons u l') l = cons u (append l' l)

-- add' z m = m
-- add' (s n') m = s (add' n' m)

-- add n m = case n of
--             z -> m
--             s n' -> s (add n' m)