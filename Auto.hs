module Auto
	where

import Data.List
import Data.Maybe
--Sequences of Distinct Names
type Name = String
type NmSeq = [String] --zakaj jih sploh rabi več?

--A imamo lahko izraz Basic X, kjer je X = Sum (Basic Y) (Basic Y), kjer je Y = Zero
--A je to zato mišljeno?
concatenation :: Name -> NmSeq -> NmSeq
concatenation x sigma = sigma ++ [x]

restriction :: Name -> NmSeq -> NmSeq
restriction x sigma = if index == Nothing then sigma else take (fromJust $ index) sigma
	where index = elemIndex x sigma

--Desribing the Regular Types
--Kako tu notri spravimo omejitev da je sigma tipa NmSeq oz Name oz. ali je to sploh treba?
data Reg = Basic Name
			| Zero
			| One
			| Sum Reg Reg
			| Product Reg Reg
			| Fix Name Reg
			| Subst Name Reg Reg -- Subst x F S ... F|_x=S
			| Weaken Name Reg -- Weaken x T .... T_x
			deriving (Show, Eq)

--a sta lahko kar funkciji? Samo potem rabimo še pripadajoče NmSeq...
--definition :: Name -> Reg sigma -> Reg sigma -> Reg sigma

--Type enviroments
--Za vsak element sigme :: NmSeq, pove kakšnega tipa je
type Env = [(Name, Reg)]

--restriction' dela podobno kot prvi restriction. Vrne seznam Env vseh elementov pred podanim imenom
--restriction' :: Name -> Env -> Env
--concatenation' doda nov element v seznam Env
--concatenation' :: (Name, Reg NmSeq) -> Env -> Env
--projection dobi ime x in okolje gamma in vrne regularni izraz ki ga x-u določa okolje gamma
--projection :: Name -> Env -> Reg

--Interpreting the Descriptions
data Term = Unit
			|Inl Term
			|Inr Term
			|Pair Term Term
			|Con Term

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
-- T = F(T) kjer je F(X) = 1 + X * X
-- T = fix (X |-> 1 + X * X)
btree = Fix "X" (Sum One (Product (Basic "X") (Basic "X")))
-- Seznam A-jev
-- data L = 1 + A * L
-- L = fix (X |-> 1 + A * X)
list a = Fix "X" (Sum One (Product a (Basic "X")))
-- Drevesa s seznami potomcev
-- data T = Item | Section [T]
-- T = fix (Y |-> 1 + [Y]) vstavimo list
-- T = fix (Y |-> 1 + fix (X |-> 1 + Y * X))
tree = Fix "Y" (Sum One (Fix "X" (Sum One (Product (Basic "Y") (Basic "X")))))

--pomožna funkcija
fresh :: [Name] -> Name
fresh xs = head $ (candidates \\ xs)
	where candidates = ["a", "b", "c", "d", "e"] ++ candidates'
		where candidates' = ["x" ++ show k | k <- [1..]]

-- seznam vseh imen (tudi vezanih s Fix), ki se pojavijo v danem tipu
-- vedno ga pokličemo s praznim seznamom
names :: Reg -> [Name] -> [Name]
names t xs = case t of
	Basic x -> x:xs
	Zero -> xs
	One -> xs
	Sum t1 t2 -> names t1 [] ++ names t2 xs
	Product t1 t2 -> names t1 [] ++ names t2 xs
	Fix x t1 -> x:names t1 xs
	Subst x t1 t2 -> names t1 [] ++ names t2 (x:xs)
	Weaken x t1 -> names t1 (x:xs)


-- za dani tip izračunaj tip poti
derive :: Name -> Reg -> Reg 
derive x (Basic y) | x == y = One
derive x (Basic y) | x /= y = Zero
derive x Zero = Zero
derive x (Sum t1 t2) = Sum (derive x t1) (derive x t2)
derive x One = Zero
derive x (Product t1 t2) = Sum (Product (derive x t1) t2) (Product t1 (derive x t2))
derive x (Fix y f) = Fix z (Sum (Weaken z (Subst y (derive x f) (Fix y f))) (Product (Weaken z (Subst y (derive y f) (Fix y f))) (Basic z)))
	where z = fresh (names f [])  -- z je ena čist nova spremenljivka
derive x (Subst y f s) = Sum (Subst y (derive x f) s) (Product (Subst y (derive y f) s) (derive x s))
derive x (Weaken y t) | x == y = Zero
derive x (Weaken y t) | x /= y = Weaken y (derive x t)

-- testni Primeri, ki kažejo, da je simplyfy nujen
-- derive "Y" tree
-- derive "X" btree