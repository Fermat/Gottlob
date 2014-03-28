module state where
prog infixr 10 >>=

Eq a b = forall C . a :: C -> b :: C


data Pair A B where
 times :: A -> B -> Pair A B
 
data Unit where
  unit :: Unit

data Nat where
  zero :: Nat
  succ :: Nat -> Nat 

data State S A where
  mkState :: (S -> Pair A S) -> State S A

returnState a = mkState (\ s . times a s)


bindState m k = mkState (\ s . case runState m s of
                              times a s' -> runState (k a) s')
runState (mkState f) = f  
fst (times a b) = a

snd (times a b) = b
plus1 n = succ n
-- State s a = s -> (a, s)
returnSt a = \ s . times a s 

(>>=) m k = \ s . case m s of
                     times a s' -> (k a) s'

getSt = \ s . times s s

putSt s' = \ s . times unit s'

-- State s a -> s -> (a, s)
runSt m s = m s

tick =  getSt >>= \ x . putSt (plus1 x) >>= \ y . returnSt x

-- tick =  getSt =>> x 
--         putSt (plus1 x) =>> y
--         returnSt x

        
-- It is all about syntactic sugar...


--tick =  bindSt getSt (\ x . bindSt (putSt (plus1 x)) (\ y . (returnSt x)))

tactic byEval t1 t2 =   
   [c] : t1 :: Q
   c1 = invbeta beta c : t2 :: Q
   c3 = ug Q . discharge c . c1
   c5 = invcmp c3 : Eq t1 t2

theorem test. Eq (snd (runSt tick (succ (succ zero))))  (succ (succ (succ zero))) 
proof
  a = byEval (snd (runSt tick (succ (succ zero))))  (succ (succ (succ zero))) 
--  b = byEval (runSt tick zero)  (succ (succ zero))
qed
                        





