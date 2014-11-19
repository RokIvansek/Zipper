module Zipper
	where

--------------------------------	
--	DREVESA, POTI IN LOKACIJE --
--------------------------------	
	
-- | Podatkovni tip s katerim predstavimo drevo.
-- | Lahko ima vrednost Item ali Section.
-- | Item je tipa String, Section pa je seznam vrednosti tipa Tree.
data Tree = Item String | Section [Tree] deriving (Show)

-- | Podatkovni tip s katerim predstavimo pot do poddrevesa.
-- | Lahko ima vrednost Top, kar pomeni, da je poddrevo kar koren drevesa.
-- | Lahko ima vrednost Node, ki je tipa trojica. 
-- | Trojica vsebuje podatke o levih sosedih (začenjajši z najbližjim), poti do očeta ter desnih sosedih (začenjajši prav tako z najbližjim). 
data Path  = Top | Node [Tree] Path [Tree] deriving (Show)

-- |Sinonim za dvojico podatkovnih tipov Tree in Path, ki predstavlja neko poddrevo, ter pot do njega.
type Location = (Tree, Path) 

---------------------------
-- PREMIKANJE PO DREVESU --
---------------------------

-- Po drevesu se premikamo z naslednjimi funkcijami.

-- | Premik levo v drevesu.
go_left :: Location -> Location
go_left (_, Top) = error "Koren nima sosedov!"
go_left (_, Node [] _ _) = error "Ni levih sosedov!"
go_left (t, Node (l:left) up right) = (l, Node left up (t:right))

-- | Premik desno v drevesu.
go_right :: Location -> Location
go_right (_, Top) = error "Koren nima sosedov!"
go_right (_, Node _ _ []) = error "Ni desnih sosedov!"
go_right (t, Node left up (r:right)) = (r, Node (t:left) up right)

-- | Premik navzgor.
go_up :: Location -> Location
go_up (_, Top) = error "Visje od korena ne gre!"
go_up (t, Node left up right) = (Section $ (reverse left) ++ (t:right),up)

-- | Premik navzdol (skrajno levo).
go_down :: Location -> Location
go_down (Item _, _) = error "Nižje od lista ne moreš!"
go_down (Section (t1:trees), p) = (t1, Node [] p trees)
go_down (_, _) = error "Poddrevo nima listov"

-- | Funkcija, s katero lahko premike pišemo v takšnem vrstnem redu, kot se dejansko premikamo po drevesu.
x -: f = f x

-- | Funkcija vrne lokacijo n-tega sina trenutnega poddrevesa.			
nth_son loc n = nth n
	where nth n
		|n == 1 = loc -: go_down
		|otherwise = if n > 0 
						then nth(n-1) -: go_right
						else error "Drugi argument mora biti naravno število!" 

{- Brez operatorja -: bi zgedala takole.
nth_son loc n = nth n
	where nth n
		|n == 1 = go_down(loc)
		|otherwise = if n > 0 
						then go_right(nth (n-1))
						else error "Drugi argument mora biti naravno število!" 
-}		

---------------------------------------------------------
-- SPREMEMBE, VSTAVLJANJE IN IZBRIS ELEMENTOV(PODDREVES) V DREVESU --
---------------------------------------------------------

-- | Celotno poddrevo na trenutni lokaciji nadomesti z nekim novim poddrevesom.
change :: Location -> Tree -> Location
change (_, p) t = (t, p)

-- | Vstavi podano podrevo desno od poddrevesa na trenutni lokaciji.
insert_right :: Location -> Tree -> Location
insert_right (t, Top) r = error "Nahajaš se na vrhu!"
insert_right (t, Node left up right) r = (t, Node left up (r:right))

-- | Vstavi podano podrevo levo od poddrevesa na trenutni lokaciji. Se ne premakne nikamor.
insert_left :: Location -> Tree -> Location
insert_left (t, Top) l = error "Nahajaš se na vrhu!"
insert_left (t, Node left up right) l = (t, Node (l:left) up right)

-- | Vstavi podano podrevo skrajno levo dol od poddrevesa na trenutni lokaciji in se pomakne v novo vstavljeno poddrevo.
insert_down :: Location -> Tree -> Location
insert_down (Item _, _) t1 = error "Nižje od lista ne moreš vstavljati!"
insert_down (Section sons, p) t1 = (t1, Node [] p sons) -: go_up

-- | Izbriše poddrevo v katerem se nahajamo, ter se premakne : v desno, če ima poddrevo desne sosede, levo če nima desnih pa ima leve sosede ali gor če nima sosedov
delete :: Location -> Location
delete (_, Top) = error "Nahajaš se na vrhu!"
delete (_, Node left up (r:right)) = (r, Node left up right)
delete (_, Node (l:left) up []) = (l, Node left up [])
delete (_, Node [] up []) = (Section [], up)




{- 
Primeri za testiranje.

let poddrevo = Item "f"
let pot = Node [Item "f"] Top [Item "g"]

go_left (poddrevo, pot)
>> (Item "f", Node [] Top [Item "f", Item "g"])

Dela pravilno. V našem preprostem drevesu smo se pomaknili levo in sedaj na levi nimamo več sosedov, 
pot do očeta je še zmeraj ista, na desni pa je sedaj poleg "g" še element "f" iz katerega smo štartali.
 
go_left $ go_left (poddrevo, pot)
*** Exception: Ni levih sosedov!

go_left (poddrevo, Top)
*** Exception: Koren nima sosedov!
-}

{- 
Primer daljšega drevesa in poti ter funkcij kako priti v Item "Haskell".
let poddrevo = Section[Item "f", Item "z", Section[Item "R", Item "Haskell"]]
let pot = Node [Item "a", Section[Item "g"]] Top [Item "b", Section[Item "g"], Item "c"]
let lokacija = (poddrevo, pot)

go_right $ go_down $ go_right $ go_right $ go_down (lokacija)

Še z operatorjem -:

lokacija -: go_down -: go_right -: go_right -: go_down -: go_right

Testiranje funkcije change in insert_
change lokacija (Section[Item "fgh", Item "kzh", Section[Item "Z", Item "Rok"]])
insert_right lokacija (Section[Item "fgh", Item "kzh", Section[Item "Z", Item "Rok"]])
insert_left lokacija (Section[Item "fgh", Item "kzh", Section[Item "Z", Item "Rok"]])
insert_down lokacija (Section[Item "fgh", Item "kzh", Section[Item "Z", Item "Rok"]])
delete lokacija

-}



























