-- Podatkovni tip, ki opisuje tipe, za katere znamo izračunati zipper

data Ty sigma = Basic sigma
              | Zero
              | One
              | Sum (Ty sigma) (Ty sigma)
              | Product (Ty sigma) (Ty sigma)
              | Fix sigma (Ty sigma)
                deriving (Show, Eq)

-- Primeri:

-- Naravna števila
-- data N = Zero | Succ N
-- N = 1 + N
-- N = F(N) kjer je F(X) = 1 + X
-- N = fix F
-- N = fix (X |-> 1 + X)
nat = Fix "X" (Sum One (Basic "X"))

-- Dvojiška drevesa
-- data T = Empty | Node T T
-- T = 1 + T * T
-- T = F(T)  kjer je F(X) = 1 + X * X
-- T = fix (X |-> 1 + X * X)
btree = Fix "X" (Sum One (Product (Basic "X") (Basic "X")))

-- Seznam A-jev
-- data L = 1 + A * L
-- L = fix (X |-> 1 + A * X)
list a = Fix "X" (Sum One (Product a (Basic "X")))

-- Drevesa s seznami potomcev
-- data T = Item | Section [T]
-- T = fix (Y |-> 1 + [Y])   vstavimo list
-- T = fix (Y |-> 1 + fix (X |-> 1 + Y * X))
tree = Fix "Y" (Sum One (Fix "X" (Sum One (Product (Basic "Y") (Basic "X")))))

-- za dani tip izračunaj tip poti
path :: Ty sigma -> Ty sigma
path (Basic _) = One
path Zero = One
path One = One
path (Sum t1 t2) = Sum (path t1) (path t2)
path (Product t1 t2) = Sum (Product (path t1) t2) (Product t1 (path t2))
path (Fix x f) = undefined
