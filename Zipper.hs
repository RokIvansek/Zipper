module Zipper
	where

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
go_down (_, _) = error "Down of empty???"

-- | Funkcija, s katero lahko premike pišemo v takšnem vrstnem redu, kot se dejansko premikamo po drevesu.
x -: f = f x


{- 
Primer za testiranje.

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
-}



























