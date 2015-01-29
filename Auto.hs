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

-- testni primeri
-- derive "Y" tree
-- derive "X" btree

--Pomožna funkcija, ki v nekem izrazu vse pojavitve spremenljivke a zamenja z b
zamenjajSprem :: Name -> Name -> Reg -> Reg
zamenjajSprem a b t = case t of
	Basic x | x == a -> Basic b
	Basic x | x /= a -> Basic x
	Zero -> Zero
	One -> One
	Sum t1 t2 -> Sum (zamenjajSprem a b t1) (zamenjajSprem a b t2)
	Product t1 t2 -> Product (zamenjajSprem a b t1) (zamenjajSprem a b t2)
	Fix x t1 | x == a -> Fix b (zamenjajSprem a b t1)
	Fix x t1 | x /= a -> Fix x (zamenjajSprem a b t1)
	Subst x t1 t2 | x == a -> Subst b (zamenjajSprem a b t1) (zamenjajSprem a b t2)
	Subst x t1 t2 | x /= a -> Subst x (zamenjajSprem a b t1) (zamenjajSprem a b t2)
	Weaken x t1 | x == a -> Weaken b (zamenjajSprem a b t1)
	Weaken x t1 | x /= a -> Weaken x (zamenjajSprem a b t1)  

--Pomožna funkcija substitute, ki izvede dejansko substitucijo v izrazu Subst
--Uporabili jo bomo v simplify. Poenostavljeni zapisi sploh ne bodo imeli Subst izrazov.
substitute :: Name -> Reg -> Reg -> Reg
substitute x t1 t2 = case t1 of
	Basic y | x == y -> t2
	Basic y | x /= y -> Basic y
	Zero -> Zero
	One -> One
	Sum t1' t2' -> Sum (substitute x t1' t2) (substitute x t2' t2)
	Product t1' t2' -> Product (substitute x t1' t2) (substitute x t2' t2)
	Fix y t | (elem y (names t2 [])) -> (substitute x (Fix a (zamenjajSprem y a t)) t2) -- primer z lista ko moramo dati vezani spremenljivki novo ime zato da ne pomešamo spremenljivk
		where a = fresh ((names t2 []) ++ (names t []))
	--Fix y t | x == y -> (substitute x t t2)  -- a je to ok? Če želimo v izrazu fix y t vse pojavitve y-a nadomestit z t2, fix izgine...tko kot substitucija v lambda računu
	Fix y t -> Fix y (substitute x t t2)
	Subst y t1' t2' -> (substitute x (substitute y t1' t2') t2)
	Weaken y t -> Weaken y (substitute x t t2)

simplify :: Reg -> Reg
simplify t = case t of
	Basic x -> Basic x
	Zero -> Zero
	One -> One
	Sum t1 t2 -> case (simplify t1, simplify t2) of
		(Zero, _) -> simplify t2
		(_, Zero) -> simplify t1
		otherwise -> Sum (simplify t1) (simplify t2)
	Product t1 t2 -> case (simplify t1, simplify t2) of
		(Zero, _) -> Zero
		(_, Zero) -> Zero
		(One, _)  -> simplify t2
		(_, One)  -> simplify t1
		otherwise -> Product (simplify t1) (simplify t2)
	Fix x t1 -> case simplify t1 of
		Zero -> Zero
		One -> One
		otherwise -> Fix x (simplify t1)
	Subst x t1 t2 | elem x (names t1 []) -> substitute x (simplify t1) (simplify t2)
	Subst x t1 t2 						 -> (simplify t1) -- ta primer zajame ničle in enke
	Weaken x t1 -> Weaken x (simplify t1)

--simplify' :: Reg -> (Reg, (Term -> Term), (Term -> Term))
