module sum where


formula infixl 3 *
-- proof infixl 3 &
-- proof pre 2 *1
-- proof pre 2 *2

data Product U V where
  times :: U -> V -> Product U V


getFist a = case a of
             times c d -> c
             
getSec a = case a of
             times c d -> d
-- logical 'and' and there
(*) U V = forall Y . (U -> V -> Y) -> Y

-- theorem testp . forall B . B
-- proof
--  [a] : Product U V
--  c = cmp a : C
-- qed
tactic and U V p1 p2 = ug Y . discharge x : U -> V -> Y . mp (mp x by p1) by p2

-- tactic (&) (p1 : U) (p2 : V) = ug Y . discharge x : U -> V -> Y . mp (mp x by p1) by p2

tactic fst U V p = mp (inst (cmp p) by U) by (discharge x : U . discharge y : V . x)

tactic sec U V p = mp (inst (cmp p) by V) by (discharge x : U . discharge y : V . y)

theorem product[Prod] . forall A B . A -> B -> A * B
proof
  [a1] : A
  [a2] : B
  c0 = and A B a1 a2 
  c = ug A . ug B . discharge a1 . discharge a2 . c0
  d = invcmp c from Prod
qed

theorem first[Fst] . forall A B . A * B -> A
proof
    [a] : A * B
    c = fst A B a
    d = ug A . ug B . discharge a . c
qed

theorem second[Sec] . forall A B . A * B -> B
proof
    [a] : A * B
    c = sec A B a
    d = ug A . ug B . discharge a . c
qed