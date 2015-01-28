module Auto
	where

import Data.List
import Data.Maybe

--Sequences  of Distinct Names
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

data Reg sigma = Basic sigma
	            | Zero
	            | One
	            | Sum (Reg sigma) (Reg sigma)
	            | Product (Reg sigma) (Reg sigma)
	            | Fix sigma (Reg sigma)
	            deriving (Show, Eq)

--Še weakening in definition je potrebno definirat

--a sta lahko kar funkciji? Samo potem rabimo še pripadajoče NmSeq...
definition :: Name -> Reg sigma -> Reg sigma -> Reg sigma


--Type enviroments
--Za vsak element sigme :: NmSeq, pove kakšnega tipa je

type Env = [(Name, Reg NmSeq)]

--restriction' dela podobno kot prvi restriction. Vrne seznam Env vseh elementov pred podanim imenom
restriction' :: Name -> Env -> Env

--concatenation' doda nov element v seznam Env
concatenation' :: (Name, Reg NmSeq) -> Env -> Env

--projection dobi ime x in okolje gamma in vrne regularni izraz ki ga x-u določa okolje gamma
projection :: Name -> Env -> Reg

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
derive :: Name -> Reg sigma -> Reg sigma
derive x (Basic [x]) = One
derive x (Basic [y]) = Zero
derive x (Zero) = Zero
derive x (Sum t1 t2) = Sum (derive x t1) (derive x t2)
derive x One = Zero
derive x (Product t1 t2) = Sum (Product (derive x t1) t2) (Product t1 (derive x t2))
derive x (Fix y (Reg y)) = undefined