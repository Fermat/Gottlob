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

data Tree U where
  leaf :: Tree U
  node :: Tree U -> U -> Tree U -> Tree U

ones1 = cons (s z) ones1
ones = let x = cons (s z) x in x

append nil l = l
append (cons u l') l = cons u (append l' l)

newapp l1 l2 = case l1 of
                    nil -> l2
                    cons u l' -> cons u (demo' l' l2)

neapp l l' = case l of
             nil -> l'
             cons u l1 -> cons u (neapp l1 l')
             

add z m = m
add (s n') m = s (add n' m)
 

mappairs f nil ys = nil
mappairs f (cons x xs) nil = nil
mappairs f (cons x xs) (cons y ys) = cons (f x y ) (mappairs f xs ys)

-- unw nil nil = a
-- unw xs ys = b xs ys


nu3 n3 = n1
nu3 a = a
nu2 n2 = n2
nu1 n1 = n1

demo f nil ys = f f ys
demo f (cons x xs) nil = f f x xs
demo f (cons x xs) (cons y ys) = f f x xs y ys


demo' f nil ys = newapp f ys
demo' f xs nil = f f xs
demo' f (cons x xs) (cons y ys) = f f x xs y ys
