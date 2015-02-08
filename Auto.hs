module Zippers
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

--Desribing the Regular Types
data Reg = Basic Name
			| Zero
			| One
			| Sum Reg Reg
			| Product Reg Reg
			| Fix Name Reg
			deriving (Show, Eq)

--Interpreting the Descriptions
data Term = Unit
			|Inl Term
			|Inr Term
			|Pair Term Term
			|Con Term
			deriving (Show, Eq)

-- Pomožna funkcija. Vzame seznam ter vrne nov (svež) string (ime spremenljivke), ki se ne pojavlja v seznamu.
fresh :: [Name] -> Name
fresh xs = head (candidates \\ xs)
	where candidates = ["a", "b", "c", "d", "e"] ++ candidates'
		where candidates' = ["x" ++ show k | k <- [1..]]

-- Names vrača seznam vseh imen (tudi vezanih s Fix), ki se pojavijo v danem tipu
names :: Reg -> [Name]
names t = case t of
	Basic x -> [x]
	Zero -> []
	One -> []
	Sum t1 t2 -> names t1 ++ names t2
	Product t1 t2 -> names t1 ++ names t2
	Fix x t1 -> x:names t1

-- Funkcija, ki za dani tip izračuna tip pripadajočega Zipper-ja
derive :: Name -> Reg -> Reg
derive x (Basic y) | x == y = One
derive x (Basic y) | x /= y = Zero
derive x Zero = Zero
derive x (Sum t1 t2) = Sum (derive x t1) (derive x t2)
derive x One = Zero
derive x (Product t1 t2) = Sum (Product (derive x t1) t2) (Product t1 (derive x t2))
derive x (Fix y f) = Fix z (Sum (substitute y (derive x f) (Fix y f)) (Product (substitute y (derive y f) (Fix y f)) (Basic z)))
	where z = fresh (y : names f)  -- z je ena čist nova spremenljivka

-- testni primeri
-- derive "Y" tree
-- derive "X" btree

--Pomožna funkcija, ki v nekem izrazu t vse pojavitve spremenljivke a zamenja z b
zamenjajSprem :: Name -> Name -> Reg -> Reg
zamenjajSprem a b t = substitute a t (Basic b)

-- Pomožna funkcija substitute, ki izvede dejansko substitucijo. Z njo smo nadomestili tip Subst.
-- Uporabili jo bomo v simplify'.
-- V izrazu t1 zamenja vse *proste* pojavitve x z izrazom t2.
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

impossible :: Term -> Term
impossible _ = error "This cannot happen"

-- Funkcija poenostavi podani tip. Zraven pa še izračuna preslikavo s katero to stori, ter njen inverz.
simplify' :: Reg -> (Reg, Term -> Term, Term -> Term)
simplify' t = case t of
	Basic x -> (Basic x, id, id)
	Zero -> (Zero, id, id)
	One -> (One, id, id)
	Sum t1 t2 -> let
					((t1', f1, g1), (t2', f2, g2)) = (simplify' t1, simplify' t2)
				 in
					case (t1', t2') of
						(Zero, _) -> (t2', unInr, \y -> Inr (g2 y)) -- Zakaj v Inr ni treba povedat tud levga elementa? S preslikavo Inr (g2 y) nismo povedal dovolj. Povedal smo samo da vstavljamo na desno stran. Ne vemo pa da je levi element t1.
							where unInr u = case u of
								Inr x -> f2 x
						(_, Zero) -> (t1', unInl, \y -> Inl (g1 y))
							where unInl u = case u of
								Inl x -> f1 x
						otherwise -> (Sum t1' t2', h1, h2)
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
				case t' of
					t1' | elem x (names t') -> (Fix x t1', h1, h2)
						where
							h1 (Con y) = Con (f y) --tuki bi mogoče še enkrat rabu kratko razlago kaj točno Con dela. Con zapakira???
							h2 (Con y) = Con (g y)
					t1' | otherwise -> (t1', h1, h2)
						where
							h1 (Con y) = f y -- Nisem čist ziher če je to OK.
							h2 y = Con (g y)

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
btree a = Fix "X" (Sum One (Product a (Product (Basic "X") (Basic "X"))))
-- Seznam A-jev
-- data L = 1 + A * L
-- L = fix (X |-> 1 + A * X)
list a = Fix "X" (Sum One (Product a (Basic "X")))
-- Drevesa s seznami potomcev
-- data T = Item | Section [T]
-- T = fix (Y |-> 1 + [Y]) vstavimo list
-- T = fix (Y |-> 1 + fix (X |-> 1 + Y * X))
tree = Fix "Y" (Sum One (Fix "X" (Sum One (Product (Basic "Y") (Basic "X")))))

-- Pomožna funkcija, ki iz trojice rezultata simplify' vrne 1. element
get_fst :: (Reg, Term -> Term, Term -> Term) -> Reg
get_fst (x, _, _) = x

-- Funkcija za testiranje pravilnosti simplify'. Če pravilno poenostavlja tipe.
test :: Reg -> Reg -> String
test t1 t2 = let
				t1' = get_fst (simplify' t1)
			 in
				if t1' == t2 then "OK" else "NI OK"
---------
--TESTI--
---------

-- test (Fix "X" (Sum (Zero) (Product (Basic "Y") (Basic "Z")))) (Product (Basic "Y") (Basic "Z"))
-- test (Sum Zero Zero) (Zero)
-- test (Product (Zero) (Basic "X")) (Zero)
-- test (Product One (Fix "X" (Sum (Basic "X") (Basic "Y")))) (Fix "X" (Sum (Basic "X") (Basic "Y")))
-- test (Fix "X" (Sum One (Fix "Z" (Product One (Basic "Y"))))) (Sum One (Basic "Y"))

-- Vsi teli zgoraj so OK!


----------------
--FUNKCIJA GEN--
----------------

-- prepletemo par seznamov med seboj
prepletemo :: [Term] -> [Term] -> [Term]
prepletemo [] ys = ys
prepletemo (x:xs) ys = x : (case ys of
								 [] -> (x:xs)
								 y:ys' -> y : prepletemo xs ys')

-- stara funkcija za prepletanje vsakega z vsakim
-- pair_vsak_z_vsakim :: [Term] -> [Term] -> [Term]
-- pair_vsak_z_vsakim xs ys = [Pair x y | x <- xs, y <- ys]

-- obdelaj par razlicno dolgih seznamov, kjer je drugi seznam daljši od prvega (predpostavi da so seznami dolzin manjsih od
-- drugega (daljsega) ze bili predhodno obdelani, in jih ni potrba ponovno)			
obd_kraj_dalj_sez :: [Term] -> [Term] -> [Term] -> [Term]
obd_kraj_dalj_sez _ [] [_] = []
obd_kraj_dalj_sez l1 [] (y:ys) = obd_kraj_dalj_sez l1 l1 ys
obd_kraj_dalj_sez l1 (x:xs) (y:ys) = Pair x y : obd_kraj_dalj_sez l1 xs (y:ys)

-- obdelaj par razlicno dolgih seznamov, kjer je  prvi seznam daljši od drugega	(predpostavi da so seznami dolzin manjsih od
-- prvega (daljsega) ze bili predhodno obdelani, in jih ni potrba ponovno)
obd_dalj_kraj_sez :: [Term] -> [Term] -> [Term] -> [Term]
obd_dalj_kraj_sez _ [_] [] = []
obd_dalj_kraj_sez l2 (x:xs) [] = obd_dalj_kraj_sez l2 xs l2
obd_dalj_kraj_sez l2 (x:xs) (y:ys) = Pair x y : obd_dalj_kraj_sez l2 (x:xs) ys
																
-- obdelaj par enako dolgih seznamov (predpostavi da so seznami dolzin manjsih od teh dveh ze bili predhodno obdelani, in jih ni
-- potrebno ponovno)																 
obd_enako_dolga_sez :: [Term] -> [Term] -> [Term]
obd_enako_dolga_sez _ [] = []
obd_enako_dolga_sez [x] (y:ys) = Pair x y : obd_enako_dolga_sez [x] ys
obd_enako_dolga_sez (x:xs) ys = Pair x (last ys) : obd_enako_dolga_sez xs ys

-- nova funkcija za prepletanje vsakega z vsakim
pair_vsak_z_vsakim' :: [Term] -> [Term] -> [Term] -> [Term] -> [Term]
pair_vsak_z_vsakim' [] [] _ _ = []
pair_vsak_z_vsakim' [] ys a _ = obd_kraj_dalj_sez a a ys
pair_vsak_z_vsakim' xs [] _ b = obd_dalj_kraj_sez b xs b
pair_vsak_z_vsakim' (x:xs) (y:ys) a b = let l1 = a ++ [x]
                                            l2 = b ++ [y]
									    in
										    obd_enako_dolga_sez l1 l2 ++ pair_vsak_z_vsakim' xs ys l1 l2

-- nastej vse elemente danega tipa, kjer imamo za vsako spremenljivko x dan seznam elementov tipa (Basic x), spravljeno v
-- asociativnem seznamu eta
-- kličemo z eta = []
gen :: [(Name,[Term])] -> Reg -> [Term]

gen eta (Basic x) = fromJust $ let k = lookup x eta
							   in case k of
								      Nothing -> error $ "Variable \"" ++ x ++ "\" not found"
								      _ -> k

gen _ Zero = []
gen _ One = [Unit]

gen eta (Sum t1 t2) = let l1 = gen eta t1
                          l2 = gen eta t2
					  in prepletemo (map Inl l1) (map Inr l2)

gen eta (Product t1 t2) = let l1 = gen eta t1
                              l2 = gen eta t2
						  in pair_vsak_z_vsakim' l1 l2 [] []

gen eta (Fix x t) = s
    where s0 = map Con $ gen ((x,[]) : eta) t
          s = case s0 of
                  [] -> []
                  _ -> nub $ prepletemo s0 (map Con $ gen ((x,s) : eta) t)

-- Primer praznega tipa: Fix "x" (Product (Basic "x") One)

-- testi za gen
{-
take 10 $ gen [] (Fix "X" (Product (Basic "X") One))
OUT: []

take 10 $ gen [] (Product (Basic "X") One)
OUT: *** Exception: Variable "X" not found

take 10 $ gen [] (Product One Zero)
OUT: []

take 10 $ gen [] (Product One One)
OUT: [Pair Unit Unit]

*Zippers> take 10 $ gen [] (One)
OUT: [Unit]

take 10 $ gen [] (Fix "X" (Sum One One))
OUT: [Con (Inl Unit),Con (Inr Unit)]

take 10 $ gen [] (Fix "X" (Product One One))
OUT: [Con (Pair Unit Unit)]

take 10 $ gen [] (Fix "X" (Sum (Basic "X") One))
OUT: [Con (Inr Unit),Con (Inl (Con (Inr Unit))),Con (Inl (Con (Inl (Con (Inr Unit))))),
Con (Inl (Con (Inl (Con (Inl (Con (Inr Unit))))))),Con (Inl (Con (Inl (Con (Inl (Con (Inl (Con (Inr Unit))))))))),
Con (Inl (Con (Inl (Con (Inl (Con (Inl (Con (Inl (Con (Inr Unit))))))))))),
Con (Inl (Con (Inl (Con (Inl (Con (Inl (Con (Inl (Con (Inl (Con (Inr Unit))))))))))))),
Con (Inl (Con (Inl (Con (Inl (Con (Inl (Con (Inl (Con (Inl (Con (Inl (Con (Inr Unit))))))))))))))),
Con (Inl (Con (Inl (Con (Inl (Con (Inl (Con (Inl (Con (Inl (Con (Inl (Con (Inl (Con (Inr Unit))))))))))))))))),
Con (Inl (Con (Inl (Con (Inl (Con (Inl (Con (Inl (Con (Inl (Con (Inl (Con (Inl (Con (Inl (Con (Inr Unit)))))))))))))))))))]

take 10 $ gen [] (Fix "X" (Sum One (Basic "X")))
OUT: [Con (Inl Unit),Con (Inr (Con (Inl Unit))),Con (Inr (Con (Inr (Con (Inl Unit))))),
Con (Inr (Con (Inr (Con (Inr (Con (Inl Unit))))))),Con (Inr (Con (Inr (Con (Inr (Con (Inr (Con (Inl Unit))))))))),
Con (Inr (Con (Inr (Con (Inr (Con (Inr (Con (Inr (Con (Inl Unit))))))))))),
Con (Inr (Con (Inr (Con (Inr (Con (Inr (Con (Inr (Con (Inr (Con (Inl Unit))))))))))))),
Con (Inr (Con (Inr (Con (Inr (Con (Inr (Con (Inr (Con (Inr (Con (Inr (Con (Inl Unit))))))))))))))),
Con (Inr (Con (Inr (Con (Inr (Con (Inr (Con (Inr (Con (Inr (Con (Inr (Con (Inr (Con (Inl Unit))))))))))))))))),
Con (Inr (Con (Inr (Con (Inr (Con (Inr (Con (Inr (Con (Inr (Con (Inr (Con (Inr (Con (Inr (Con (Inl Unit)))))))))))))))))))]

take 10 $ gen [] (Fix "X" (Sum (Sum One (Basic "X")) (Basic "X")))
OUT: [Con (Inl (Inl Unit)),Con (Inr (Con (Inl (Inl Unit)))),Con (Inl (Inr (Con (Inl (Inl Unit))))),
Con (Inr (Con (Inr (Con (Inl (Inl Unit)))))),Con (Inl (Inr (Con (Inr (Con (Inl (Inl Unit))))))),
Con (Inr (Con (Inl (Inr (Con (Inl (Inl Unit))))))),Con (Inl (Inr (Con (Inl (Inr (Con (Inl (Inl Unit)))))))),
Con (Inr (Con (Inr (Con (Inr (Con (Inl (Inl Unit)))))))),Con (Inl (Inr (Con (Inr (Con (Inr (Con (Inl (Inl Unit))))))))),
Con (Inr (Con (Inl (Inr (Con (Inr (Con (Inl (Inl Unit)))))))))]

take 10 $ gen [] (Fix "X" (Product (Basic "X") One))
take 10 $ gen [] (Fix "X" (Product One (Basic "X")))
OUT: []

take 10 $ gen [] (Fix "X" (Sum Zero One))
OUT: [Con (Inr Unit)]

take 10 $ gen [] (Fix "X" (Sum (Product (Basic "X") One) One))
OUT: [Con (Inr Unit),Con (Inl (Pair (Con (Inr Unit)) Unit))*** Exception: <<loop>> -> Potrebno nekako preprečiti neskoncno zanko 
(te izjeme se ne da ujeti)

take 10 $ gen [] (Fix "X" (Sum (Product One (Basic "X")) One))
[Con (Inr Unit),Con (Inl (Pair Unit (Con (Inr Unit)))),Con (Inl (Pair Unit (Con (Inl (Pair Unit (Con (Inr Unit))))))),
Con (Inl (Pair Unit (Con (Inl (Pair Unit (Con (Inl (Pair Unit (Con (Inr Unit)))))))))),
Con (Inl (Pair Unit (Con (Inl (Pair Unit (Con (Inl (Pair Unit (Con (Inl (Pair Unit (Con (Inr Unit))))))))))))),
Con (Inl (Pair Unit (Con (Inl (Pair Unit (Con (Inl (Pair Unit (Con (Inl (Pair Unit (Con (Inl (Pair Unit (Con (Inr Unit)))))))))))))))),
Con (Inl (Pair Unit (Con (Inl (Pair Unit (Con (Inl (Pair Unit (Con (Inl (Pair Unit (Con (Inl (Pair Unit (Con (Inl (Pair Unit (Con (Inr Unit))))))))))))))))))),
Con (Inl (Pair Unit (Con (Inl (Pair Unit (Con (Inl (Pair Unit (Con (Inl (Pair Unit (Con (Inl (Pair Unit (Con (Inl (Pair Unit (Con (Inl (Pair Unit (Con (Inr Unit)))))))))))))))))))))),
Con (Inl (Pair Unit (Con (Inl (Pair Unit (Con (Inl (Pair Unit (Con (Inl (Pair Unit (Con (Inl (Pair Unit (Con (Inl (Pair Unit (Con (Inl (Pair Unit (Con (Inl (Pair Unit (Con (Inr Unit))))))))))))))))))))))))),
Con (Inl (Pair Unit (Con (Inl (Pair Unit (Con (Inl (Pair Unit (Con (Inl (Pair Unit (Con (Inl (Pair Unit (Con (Inl (Pair Unit (Con (Inl (Pair Unit (Con (Inl (Pair Unit (Con (Inl (Pair Unit (Con (Inr Unit))))))))))))))))))))))))))))]

take 10 $ gen [] (Fix "X" (Sum One Zero))
OUT: [Con (Inl Unit)]

take 10 $ gen [] (Fix "X" (Sum One (Product One (Basic "X"))))
[Con (Inl Unit),Con (Inr (Pair Unit (Con (Inl Unit)))),Con (Inr (Pair Unit (Con (Inr (Pair Unit (Con (Inl Unit))))))),
Con (Inr (Pair Unit (Con (Inr (Pair Unit (Con (Inr (Pair Unit (Con (Inl Unit)))))))))),
Con (Inr (Pair Unit (Con (Inr (Pair Unit (Con (Inr (Pair Unit (Con (Inr (Pair Unit (Con (Inl Unit))))))))))))),
Con (Inr (Pair Unit (Con (Inr (Pair Unit (Con (Inr (Pair Unit (Con (Inr (Pair Unit (Con (Inr (Pair Unit (Con (Inl Unit)))))))))))))))),
Con (Inr (Pair Unit (Con (Inr (Pair Unit (Con (Inr (Pair Unit (Con (Inr (Pair Unit (Con (Inr (Pair Unit (Con (Inr (Pair Unit (Con (Inl Unit))))))))))))))))))),
Con (Inr (Pair Unit (Con (Inr (Pair Unit (Con (Inr (Pair Unit (Con (Inr (Pair Unit (Con (Inr (Pair Unit (Con (Inr (Pair Unit (Con (Inr (Pair Unit (Con (Inl Unit)))))))))))))))))))))),
Con (Inr (Pair Unit (Con (Inr (Pair Unit (Con (Inr (Pair Unit (Con (Inr (Pair Unit (Con (Inr (Pair Unit (Con (Inr (Pair Unit (Con (Inr (Pair Unit (Con (Inr (Pair Unit (Con (Inl Unit))))))))))))))))))))))))),
Con (Inr (Pair Unit (Con (Inr (Pair Unit (Con (Inr (Pair Unit (Con (Inr (Pair Unit (Con (Inr (Pair Unit (Con (Inr (Pair Unit (Con (Inr (Pair Unit (Con (Inr (Pair Unit (Con (Inr (Pair Unit (Con (Inl Unit))))))))))))))))))))))))))))]

take 10 $ gen [] (Fix "X" (Sum One (Product (Basic "X") One)))
[Con (Inl Unit),Con (Inr (Pair (Con (Inl Unit)) Unit))*** Exception: <<loop>> -> Enaka izjema kot zgoraj
-}

