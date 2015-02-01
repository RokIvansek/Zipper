module Auto
	where

-- IDEJE:
-- 1. Weaken je samo za birokracijo (katere spremenljivke so veljavne) in ga pobrišemo
-- 2. Subst pobrišemo iz tipa in njegovo uporabo v derive od Fix nadomestimo s substitute
-- 3. Do konca napiši simplify' (ko dela, lahko simplify pobrišeš)
-- 4. Testi, da simplify' pravilno deluje:
--    * pravilno poenostavlja tipe
--    * pravilno izračuna izomorfizme (preizkusimo na primerih)

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
names :: Reg -> [Name]
names t = case t of
	Basic x -> [x]
	Zero -> []
	One -> []
	Sum t1 t2 -> names t1 ++ names t2
	Product t1 t2 -> names t1 ++ names t2
	Fix x t1 -> x:names t1
	--Subst x t1 t2 -> x : names t1 ++ names t2
	--Weaken x t1 -> x : names t1


-- za dani tip izračunaj tip poti
derive :: Name -> Reg -> Reg
derive x (Basic y) | x == y = One
derive x (Basic y) | x /= y = Zero
derive x Zero = Zero
derive x (Sum t1 t2) = Sum (derive x t1) (derive x t2)
derive x One = Zero
derive x (Product t1 t2) = Sum (Product (derive x t1) t2) (Product t1 (derive x t2))
derive x (Fix y f) = Fix z (Sum (substitute y (derive x f) (Fix y f)) (Product (substitute y (derive y f) (Fix y f)) (Basic z)))
	where z = fresh (y : names f)  -- z je ena čist nova spremenljivka
--derive x (Subst y f s) = Sum (Subst y (derive x f) s) (Product (Subst y (derive y f) s) (derive x s))
--derive x (Weaken y t) | x == y = Zero
--derive x (Weaken y t) | x /= y = Weaken y (derive x t)

-- testni primeri
-- derive "Y" tree
-- derive "X" btree

--Pomožna funkcija, ki v nekem izrazu t vse pojavitve spremenljivke a zamenja z b
zamenjajSprem :: Name -> Name -> Reg -> Reg
zamenjajSprem a b t = substitute a t (Basic b)

-- Pomožna funkcija substitute, ki izvede dejansko substitucijo v izrazu Subst
-- Uporabili jo bomo v simplify. Poenostavljeni zapisi sploh ne bodo imeli Subst izrazov.
-- V izrazu t1 zamenjaj vse *proste* pojavitve x z izrazom t2.
-- Hkrati odpravimo vse notranje Subst (notranjih Subst (in Subst-ov na sploh) sedaj ni več ker smo Subst odstranili iz definicije tipov)
substitute :: Name -> Reg -> Reg -> Reg
substitute x t1 t2 = case t1 of
	Basic y | x == y -> t2
	Basic y | x /= y -> Basic y
	Zero -> Zero
	One -> One
	Sum t1' t2' -> Sum (substitute x t1' t2) (substitute x t2' t2)
	Product t1' t2' -> Product (substitute x t1' t2) (substitute x t2' t2)
	Fix y t | (elem y (names t2)) -> (substitute x (Fix a (zamenjajSprem y a t)) t2) -- primer z lista ko moramo dati vezani spremenljivki novo ime zato da ne pomešamo spremenljivk
		where a = fresh ((names t2) ++ (names t))
	Fix y t -> Fix y (substitute x t t2)
	--Subst y t1' t2' -> (substitute x (substitute y t1' t2') t2)
	--Weaken y t -> Weaken y (substitute x t t2) -- XXX je se vedno neodvisno od y (zakaj rabimo Weaken?)

simplify :: Reg -> Reg
simplify t = case t of
	Basic x -> Basic x
	Zero -> Zero
	One -> One
	Sum t1 t2 -> case (simplify t1, simplify t2) of
		(Zero, t2') -> t2' -- XXX podobno popravi ostale primere
		(t1', Zero) -> t1'
		(t1', t2') -> Sum t1' t2'
	Product t1 t2 -> case (simplify t1, simplify t2) of
		(Zero, _) -> Zero
		(_, Zero) -> Zero
		(One, t2') -> t2'
		(t1', One) -> t1'
		otherwise -> Product (simplify t1) (simplify t2)
	Fix x t1 -> case simplify t1 of
		t1' | elem x (names t1') -> Fix x t1'
		t1' | otherwise -> t1'
	--Subst x t1 t2 -> simplify (substitute x (simplify t1) (simplify t2))
	--Weaken x t1 -> Weaken x (simplify t1)

impossible :: Term -> Term
impossible _ = error "This cannot happen"

simplify' :: Reg -> (Reg, Term -> Term, Term -> Term)
simplify' t = case t of
	Basic x -> (Basic x, id, id)
	Zero -> (Zero, id, id)
	One -> (One, id, id)
	Sum t1 t2 -> let
					((t1', f1, g1), (t2', f2, g2)) = (simplify' t1, simplify' t2)
				 in 
					case (t1', t2') of
						(Zero, t2') -> (t2', unInr, \y -> Inr (g2 y)) -- XXX podobno popravi ostale primere -- Zakaj v Inr ni treba povedat tud levga elementa? S preslikavo Inr (g2 y) nismo povedal dovolj. Povedal smo samo da vstavljamo na desno stran. Ne vemo pa da je levi element t1.
							where unInr u = case u of
								Inr x -> f2 x
						(t1', Zero) -> (t1', unInl, \y -> Inl (g1 y))
							where unInl u = case u of
								Inl x -> f1 x
						(t1', t2') -> (Sum t1' t2', h1, h2)
							where 
								h1 u = case u of
									Inl x -> Inl (f1 x)
									Inr x -> Inr (f2 x)
								h2 u = case u of
									Inl x -> Inl (g1 x)
									Inr x -> Inr (g2 x)
	Product t1 t2 -> let 
						((t1', f1, g1), (t2', f2, g2)) = (simplify' t1, simplify' t2)
					 in 
						case (t1', t2') of
							(Zero, _) -> (Zero, impossible, impossible)
							(_, Zero) -> (Zero, impossible, impossible)
							(One, _)  -> (t2', h1, (\y' -> Pair Unit (g2 y')))
								where h1 u = case u of
									Pair x y -> f2 y
							(_, One)  -> (t1', h1, (\y' -> Pair (g1 y') Unit))
								where h1 u = case u of
									Pair x y -> f1 x
							otherwise -> (Product t1' t2', h1, h2)
								where
									h1 u = case u of
										Pair x y -> Pair (f1 x) (f2 y)
									h2 u = case u of
										Pair x y -> Pair (g1 x) (g2 y)
	Fix x t -> let 
				(t', f, g) = simplify' t
			   in
				case t of
					t1' | elem x (names t') -> (Fix x t1', h1, h2)
						where
							h1 (Con y) = Con (f y) --tuki bi mogoče še enkrat rabu kratko razlago kaj točno Con dela. Con zapakira???
							h2 (Con y) = Con (g y) --zakaj je tu parse error??!%##%#$!!"$#$"#$#"#
					t1' | otherwise -> (t1', h1, h2)
						where
							h1 (Con y) = f y -- Nisem čist ziher če je to OK.
							h2 y = Con (g y)                    

{-
-- nastej vse elemente danega tipa, kjer imamo za vsako spremenljivko x dan seznam
-- elementov tipa (Basic x), spravljeno v asociativnem seznamu eta
gen :: Reg -> [Term]
gen _ Zero = []
gen _ One = [Unit]

gen eta (Sum t1 t2) = let l1 = gen eta t1
						  l2 = gen eta t2
					  in prepletemo (map Inl l1) (map Inr l2)

gen eta (Product t1 t2) = let l1 = gen eta t1
							  l2 = gen eta t2
						  in Pair_vsak_z_vsakim l1 l2

get eta (Fix x t) = s
  where s0 = map Con $ generate ((x,[]) : eta) t
		s = case s0 of
				[] -> []
				_ -> s0 ++ (map Con $ generate ((x,s) : eta) t)
				   -- namesto ++ v prejsni vrtici uporabi "prepletemo"?
				   -- pozor, prepletemo l1 l2 mora začeti z l1

-- Primer praznega tipa: Fix "x" (Product (Basic "x") One)
-}