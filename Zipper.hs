module Zipper
	where

--------------------------------	
--	DREVESA, POTI IN LOKACIJE --
--------------------------------	
	
-- | Podatkovni tip s katerim predstavimo drevo.
-- | Lahko ima vrednost Item ali Section.
-- | Item je tipa String, Section pa je seznam vrednosti tipa Tree.
-- Načeloma bi lahko konstruktor Item vzel poljuben tip (Int, Bool, ...)
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

---------------------------------------------------------------------
-- SPREMEMBE, VSTAVLJANJE IN IZBRIS ELEMENTOV(PODDREVES) V DREVESU --
---------------------------------------------------------------------

-- | Celotno poddrevo na trenutni lokaciji nadomesti z nekim novim poddrevesom.
change :: Location -> Tree -> Location
change (_, p) t = (t, p)

-- | Vstavi podano podrevo desno od poddrevesa na trenutni lokaciji. Fokus ostane isti.
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

-- | Izbriše poddrevo v katerem se nahajamo, ter se premakne: 
-- | *v desno, če ima poddrevo desne sosede,
-- | *levo če nima desnih pa ima leve sosede ali 
-- | *gor če nima sosedov.
delete :: Location -> Location
delete (_, Top) = error "Nahajaš se na vrhu!"
delete (_, Node left up (r:right)) = (r, Node left up right)
delete (_, Node (l:left) up []) = (l, Node left up [])
delete (_, Node [] up []) = (Section [], up)

-----------
-- SCARS --
-----------

-- | Implementiramo novo drevo, ki podatke hrani na malo drugačen način.
-- | Lahko ima vrednost Item ali Siblings. V Siblings je prvi seznam, seznam levih sosedov elementa
-- | Memo_tree, drugi seznam pa seznam desnih sosedov.
-- | Item je tipa String, Siblings pa je trojka seznam Memo dreves * Memo drevo * seznam Memo dreves.
data Memo_Tree = Memo_Item String | Siblings [Memo_Tree] Memo_Tree [Memo_Tree] deriving (Show)

-- | Podatkovni tip s katerim predstavimo pot do poddrevesa.
-- | Lahko ima vrednost Top, kar pomeni, da je poddrevo kar koren drevesa.
-- | Lahko ima vrednost Node, ki je tipa trojica. 
-- | Trojica vsebuje podatke o levih sosedih (začenjajši z najbližjim), poti do očeta ter desnih sosedih (začenjajši prav tako z najbližjim). 
data Memo_Path  = Memo_Top | Memo_Node [Memo_Tree] Memo_Path [Memo_Tree] deriving (Show)

-- |Sinonim za dvojico podatkovnih tipov Tree in Path, ki predstavlja neko poddrevo, ter pot do njega (njegov Zipper).
type Memo_Location = (Memo_Tree, Memo_Path) 

-- | Funkcije za premik navzgor in navzdol so sedaj enostavnejše.

-- | Premik navzgor.
go_up_memo :: Memo_Location -> Memo_Location
go_up_memo (_, Memo_Top) = error "Visje od korena ne gre!"
go_up_memo (t, Memo_Node left p' right) = (Siblings left t right, p')

-- | Premik navzdol (skrajno levo).
go_down_memo :: Memo_Location -> Memo_Location
go_down_memo (Memo_Item _, _) = error "Nižje od lista ne moreš!"
go_down_memo (Siblings left t' right, p) = (t', Memo_Node left p right)

---------------------
-- BINARNA DREVESA --
---------------------

-- Binarno drevo
data Binary_Tree = Nil | Cons Binary_Tree Binary_Tree

-- Pripadajoči zipper. 
-- Pove korak (Left ali Right) in katero je drevo, ki vanj nismo šli
data Binary_Path = Binary_Top | L Binary_Path Binary_Tree | R Binary_Tree Binary_Path

-- Lokacija. Drevo, na katerega se fokusiramo in njegov zipper
type Binary_Location = (Binary_Tree, Binary_Path)

-- Funkcije

change_binary :: Binary_Location -> Binary_Tree -> Binary_Location
change_binary (_, p) t = (t, p)

go_left_binary :: Binary_Location -> Binary_Location
go_left_binary (_, Binary_Top) = error "Koren je en sam, Oče vseh!"
go_left_binary (t, L father right) = error "Si že v levem kraku"
go_left_binary (t, R left father) = (left, L father t)

go_up_binary :: Binary_Location -> Binary_Location
go_up_binary (_, Binary_Top) = error "Višje od očeta vseh ne moreš. On je najvišji."
go_up_binary (t, L father right) = (Cons t right, father)
go_up_binary (t, R left father) = (Cons left t, father)
























