----------------------------
-- Primeri za testiranje. --
----------------------------

let poddrevo = Item "f"
let pot = Node [Item "f"] Top [Item "g"]

go_left (poddrevo, pot)
-- >> (Item "f", Node [] Top [Item "f", Item "g"])

-- Dela pravilno. V našem preprostem drevesu smo se pomaknili levo in sedaj na levi nimamo več sosedov, 
-- pot do očeta je še zmeraj ista, na desni pa je sedaj poleg "g" še element "f" iz katerega smo štartali.
 
go_left $ go_left (poddrevo, pot)
-- *** Exception: Ni levih sosedov!

go_left (poddrevo, Top)
-- *** Exception: Koren nima sosedov!


-- Primer daljšega drevesa in poti ter funkcij kako priti v Item "Haskell".
let poddrevo = Section[Item "f", Item "z", Section[Item "R", Item "Haskell"]]
let pot = Node [Item "a", Section[Item "g"]] Top [Item "b", Section[Item "g"], Item "c"]
let lokacija = (poddrevo, pot)

go_right $ go_down $ go_right $ go_right $ go_down (lokacija)

-- Še z operatorjem -:

lokacija -: go_down -: go_right -: go_right -: go_down -: go_right

-- Testiranje funkcije change in insert_
change lokacija (Section[Item "fgh", Item "kzh", Section[Item "Z", Item "Rok"]])
insert_right lokacija (Section[Item "fgh", Item "kzh", Section[Item "Z", Item "Rok"]])
insert_left lokacija (Section[Item "fgh", Item "kzh", Section[Item "Z", Item "Rok"]])
insert_down lokacija (Section[Item "fgh", Item "kzh", Section[Item "Z", Item "Rok"]])
delete lokacija

