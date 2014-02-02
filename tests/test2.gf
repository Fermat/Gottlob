data Nat = z :: Nat
         | s :: Nat -> Nat

data Nat where
  z :: Nat
  s :: Nat -> Nat

data List U where
  nil :: List U
  cons :: U -> List U -> List U

data Vec U a = vnil :: Vec U 0
         | vcons :: (n :: Nat) -> U -> Vec U n -> Vec U (S n) 

   
add n m = 
  case n of
     Z -> m
     S n' -> S (add n' m)

theorem ind : forall C.Z :: C -> (forall y :: C -> S y :: C) -> (forall m :: Nat => m :: C)
proof.  
       C : Ind -> Form
       [a1] : Z::C
       [a2] : forall y :: C -> S y :: C
       [a3] : m :: Nat
       b1 = cmp a3 : forall C . Z :: C -> (forall y :: C -> S y :: C) -> m :: C
       b2 = inst b1 C : Z :: C -> (forall y :: C -> S y :: C) -> m :: C
       b3 = mp b2 a1 : (forall y :: C -> S y :: C) -> m :: C
       b4 = mp b3 a2 : m :: C
       b5 = discharge a3 b4 : m :: Nat -> m :: C
       b6 = ug m b5 : forall m :: Nat -> m :: C
       b7 = discharge a2 b6 : (forall y :: C -> S y :: C) -> forall m :: Nat -> m :: C
       b8 = discharge a1 b7 : Z::C -> (forall y :: C -> S y :: C) -> forall m :: Nat -> m :: C
       b9 = ug C b8 : forall C. Z::C -> (forall y :: C -> S y :: C) -> forall m :: Nat -> m :: C
qed.

-- b9 = 
--ug C (dis a1 (dis a2 (ug m (dis a3 (mp (mp (Inst (cmp a3) C) a1) a2)))))
-- so what? proof have computational content. 
-- formula abriviation

t1 == t2 := forall C. t1::C -> t2::C

theroem sym : forall x y z. x == y -> y == z -> x == z
proof. 
     [a1] : x == y
     [a2] : y == z
     b1 = cmp a1 : forall C. x::C -> y::C
     b2 = cmp a2 : forall C. y::C -> z::C
     b3 = inst b1 C : x::C -> y::C
     b4 = inst b2 C : y::C -> z::C 
     [c] : x :: C
     c1 = mp b3 c : y :: C
     c2 = mp b4 c1 : z :: C
     d = ug C (discharge c c2) : forall C. x::C -> z::C
     e = invcmp d : x == z
     -- c = invcmp e : m
     f = discharge a1 (discharge a2 e) : sym
qed. 

theorem addn : forall x :: Nat -> add x Z = x
proof.
        p = inst ind (iota q . add q Z = q) : 
        b = eval : add Z Z = Z
        [c1] : add n Z == n 
        c2 = eval : add (S n) Z == S (add n Z) 
        c3 = cong S c1 : S (add n Z) == S n  
        c4 = trans c2 c3 : add (S n) Z == S n
        b2 = ug (discharge c1 c4) : forall n.(add n Z == n -> add Sn Z == Sn)
        p b2 b
qed.
