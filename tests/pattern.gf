module pattern where

data Nat where
  z :: Nat
  s :: Nat -> Nat 

data List U where
  nil :: List U
  cons :: U -> List U -> List U

data Nuts where
  n1 :: Nuts
  n2 :: Nuts
  n3 :: Nuts
  deriving Ind  

append nil l = l
append (cons u l') l = cons u (append l' l)

neapp l l' = case l of
             nil -> l'
             cons u l1 -> cons u (neapp l1 l')
             
data Tree U where
  leaf :: Tree U
  node :: Tree U -> U -> Tree U -> Tree U

{-
add z m = m
add (s n') m = s (add n' m)
 

mappairs f nil ys = nil
mappairs f (cons x xs) nil = nil
mappairs f (cons x xs) (cons y ys) = cons (f x y ) (mappairs f xs ys)

unw nil nil = a
unw xs ys = b xs ys
-}

nu3 n3 = n1
nu3 a = a
-- nu2 n2 = n2
-- nu1 n1 = n1

-- demo f nil ys = a f ys
-- demo f (cons x xs) nil = b f x xs
-- demo f (cons x xs) (cons y ys) = c f x xs y ys


demo' f nil ys = a f ys
demo' f xs nil = b f xs
demo' f (cons x xs) (cons y ys) = c f x xs y ys
newapp l1 l2 = case l1 of
                    nil -> l2
                    cons u l' -> cons u (newapp l' l2)
