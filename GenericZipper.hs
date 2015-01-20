-- za (en na�in) uporabe forall
{-# LANGUAGE Rank2Types, GADTs #-}
-- za uporabo generic Data razreda in druge datatype-e, ki so generic, prav tako za tak�ne funkcije
{-# LANGUAGE DeriveDataTypeable #-}

import Data.Generics

-- ZADRGA IN NJEN KONTEKST

-- Generi�na zadrga; sestavljena je iz luknje in njenega konteksta. Podatek je lahko lahko kakr�negakoli tipa, ki raz�irja 
-- Tip luknje (raz�irja generi�ni tip/razred Data) je lahko razli�en ob spremembi fokusa (luknje) zadrge.
data Zipper root =
  forall hole. (Data hole) =>
    Zipper hole (Context hole root)
	
-- Kontekst predstavlja "one-hole" kontekst, ki vsebuje luknjo in najvi�je/korensko vozli��e zadrge. �e je luknja v najvi�jem 
-- vozli��u drevesa, potem je kontekst prazen, sicer pa vsebuje mnozico levih in desnih sosedov luknje ter star�evski kontekst 
-- trenutnega.
-- Tip/zaporedje tipov luknje od star�evskega konteksta se mora ujemati z tipom/zaporedjem tipov, ki je zgrajen iz ToLeft in ToRight 
-- sosednjih vozli��, torej parent parameter od ToRight je konstruktor, ki mu manjka nek parameter, ta parameter predstavlja hole, in
-- temu tipu mora ustrezati tip luknje star�evskega konteksta; s tem ko funkciji posredujemo funkcijo zmanjkajo�im parametrom, se 
-- nato zapolni �e ta manjkajo�ia argument.
-- Nov kontekst ustvarimo z ujemajocimi ToLeft in ToRight sosednjimi vozli��i ter s trenutno luknjo zadrge, ki se zdru�ijo in tako 
-- predstavljajo novo luknjo v star�evskem kontekstu (parent parameter). Root parameter konteksta je vedno enak korenu drevesa.
data Context hole root where
  CntxNull :: Context var var
  CntxCons :: forall rightArgs parent hole root. (Data parent) =>
	ToLeft (hole -> rightArgs) -> ToRight rightArgs parent -> Context parent root -> Context hole root 

-- KONSTRUKTI ZA LUKNJI VZPOREDNA LEVA IN DESNA VOZLI��A	
		
-- Vsebuje leve sosede trenutne luknje zadrge. (Leva) vozli��a veri�imo z virtualnimi aplikacijami za vsak argument konstruktorja 
-- nekega tipa od najbolj levega do najbolj desnega (torej argumente poljubnega datatype-a povrsti pisemo med ToLeftCons 
-- construktorji, sam konstruktor pa kli�emo z ToLeftUnit).
-- Veriga virtualnih aplikacij je torej odvisna od poljubnega tipa, ki ga temu constructorju posredujemo.
-- Vrne funkcijo oz. konstruktor; lahko se zgodi da �e potrebuje manjkajo�e parametre z desne strani.
-- Gre rekurzivno do max globine, vrne funkcijo/konstruktor v max globini, z vracanjem pa konstruktorju polni argumente 
-- (od najbolj levega do najbolj desnega izmed tistih, ki so pred oz. levo od luknje)
-- Ko prispemo do konstruktorja, ga vrnemo
data ToLeft leftArgs
  = ToLeftUnit leftArgs 
  | forall leftArg. (Data leftArg) => 
	  ToLeftCons (ToLeft (leftArg -> leftArgs)) leftArg 

-- ToRight tip predstavlja vozli��a desno od trenutne luknje zadrge; ki bodo priskrbljena nekemu konstruktorju. (Desna) vozli��a 
-- shranjujmo od najbolj desnega do najbolj levega (torej argumente poljubnega tipa povrsti v obratnem vrstnem redu pisemo med 
-- ToRightCons konstruktorji)
-- ToRight objekt priskrbi vrednosti, ki jih nek konstruktor sprejme kot argumente z desne strani trenutne luknje.
-- parent parameter zagotavlja da se tipi kontekstov ujemajo.
-- Vrne isto kot ToLeft (Konstruktor z manjkajo�imi parametri (le enim ali nobenim, ToLeft pa lahko z ve�im)), le da vrne zraven �e en 
-- parameter ob vseh parametrih konstruktorja, ki je prosta spremenljivka, kamor se shrani rezultat konstrukta (ko le-ta prejme 
-- vse argumente) - right.
-- Gre rekurzivno do max globine, vrne prosti spremenljivki/variabili v max globini, z vracanjem polni argumente (od najbolj 
-- desnega do najbolj levega (ki je �e za oz. desno od luknje))
-- �e ni desnega vozli��a od trenutnega, pripni prazno/null vozlisce
data ToRight rightArgs parent where
  ToRightNull :: ToRight parent parent 
  ToRightCons :: (Data rightArg) => 
	rightArg -> ToRight leftCons right -> ToRight (rightArg -> leftCons) right

-- DEKONSTRUKTI ZA LUKNJI VZPOREDNA LEVA IN DESNA VOZLI��A	

-- Zgradi construktor nekega tipa, preko parametrov ki so shranjeni v verigi constructorjev zadrg.
-- Pri dekonstrukciji verige konstruktorejv, dobis z dekonsrukcijo po vrsti od najbolj desnegna proti levemu konstruktu nazaj 
-- parametre, na koncu pa tudi sam kosntruktor poljubnega tipa, ki je bil podan.
-- ko pridemo do dna rekurzije, le poklicemo funkcijo oz. natanceje konstruktor, z vracanjem pa ga polnimo s parametri preko 
-- spodnjega konstruktorja.
fromLeft :: ToLeft l -> l
fromLeft (ToLeftUnit leftArg) = leftArg
fromLeft (ToLeftCons left leftArg) = fromLeft left leftArg

-- Prejme neko funkcijo (natancneje konstruktor), ki ima lahko ali nic parametrov, ali p ajih ima ze nekaj z leve strani luknje 
-- (s fromLeft smo lohko napolnili in potem posredovali fromRight, kateri posreduje (z desne strani) manjkajoce) parametre, 
-- shranjene v verigi constructorjev zadrge
-- parent je naslednjo desno vozlisce
-- ce pridemo do konca desne strani, samo vrni kar mas, ker to je sestavljen construktor z vsemi parametri
-- Za razliko od fromLeft se fromRight evaluira iterativno ker fromLeft potrebuje prvo priti do koncne globine, kjer sprozi 
-- konstruktor, nato pa temu konstruktorju polni parametre, fromRight pa to polnjenju parametrov samo nadaljuje (ne rabi pridt do 
-- koncne glbine kot fromLeft, ker je to ze naredil fromLeft), ko pa pride do konca, torej, ko poda konstruktorju vse parametre, 
-- pa samo vrne ta konstruktor (zadnji element je ToRightNull)
fromRight :: r -> ToRight r parent -> parent 
fromRight rightCons (ToRightNull) = rightCons 
fromRight leftCons (ToRightCons rightArg right) = fromRight (leftCons rightArg) right 

-- Zdruzi trenutno luknjo, leva in desna vozli��a v novo luknjo (potrebno pri pomiku po zadrgi navzgor) - "zazippamo" trenutno 
-- luknjo in tako dobimo novo, ki je star�evska prej�nji.
-- Najprej z fromLeft pridobi vse vrednosti iz verige ToLeft (iz verige klicanih konstruktorjev, parameter lefts), nato pa jih 
-- uporabi kot argumente v verigi ToRight.
-- Parameter t pri ToRight rabimo tu, ker z fromLeft (preko ToLeft) dobimo konstruktor z manjkajocimi parametri (ni nujno, lahko ma ze
-- vse parametre, odvisno od lokacije luknje), ki jih tu dopolnimo z vsemi manjkajo�imi parametri. 
-- S signaturo povemoo, da ToLeft sprejme luknjo, in da to kar vrne ToLeft, mora biti istga tipa, kar sprejme ToRight kot prvi 
-- parameter, njegov drugi parameter pa mora biti istega tipa kot vrednost, ki jo vrne ta funkcija (vrne celotno zaporedje tipov 
-- nekega konstruktorja); parent parameter je eksistencialo omejen oz ima omejeno tipizacijo, da lahko le ta ustreza poljubnemu 
-- tipu.
-- Z fromLeft zapolni parametre konstruktorju nekega tipa levo od luknje, potem podamo luknjo taistemu konstructorju, nato pa 
-- fromRight zapolni taistemu constructorju �e parametre desno od luknje.
zipHole :: ToLeft (hole -> rightArgs) -> hole -> ToRight rightArgs parent -> parent
zipHole leftArgs hole rightArgs =
  fromRight ((fromLeft leftArgs) hole) rightArgs

-- Torej ToLeft in ToRight zapakerata parametre konstruktorja nekega tipa, fromLeft in fromRight pa to odpakerata/rekonstruirata in 
-- skupaj z luknjo sestavita (preko zipHole) v nek tip/v surovi podatek (torej v podatek, ki ni razcelenjen preko ToLeft, ToRight in 
-- Context konstruktorjev zadrge)

-- FUNKCIJE ZA PREMIKANJE PO ZADRGI

moveLeft, moveRight, moveUp, moveDown :: Zipper a -> Maybe (Zipper a)

-- Vzame/odstrani ToLeftCons iz levega dela konteksta in doda ToRightCons v desni del konteksta
-- �e je kontekst prazen, ne moremo levo
-- �e ni vec levih vozli��, ne moremo levo
-- hole' je naslednji levi element/sibling, left so pa usi ostali levi siblingi, ki so levo od hole' siblinga. Ker smo se premaknili levo, 
-- moramo staro luknjo hole dati na desno stran nove luknje hole'
moveLeft (Zipper _ CntxNull) = Nothing 
moveLeft (Zipper _ (CntxCons (ToLeftUnit _) _ _)) = Nothing 
moveLeft (Zipper hole (CntxCons (ToLeftCons left hole') right cntx)) = 
  Just (Zipper hole' (CntxCons left (ToRightCons hole right) cntx)) 
  
-- vzame/odstrani ToRightCons iz desnega dela konteksta in doda ToLeftCons v levi del konteksta.
-- �e je kontekst prazen, ne moremo desno
-- �e ni vec desnih vozli��, ne moremo desno
-- hole' je naslednji desni element/sibling, right so pa usi ostali desni siblingi, ki so desno od hole' siblinga. Ker smo se premaknili 
-- desno, moramo staro luknjo hole dati na levo stran nove luknje hole'
moveRight (Zipper _ CntxNull) = Nothing 
moveRight (Zipper _ (CntxCons _ ToRightNull _)) = Nothing 
moveRight (Zipper hole (CntxCons left (ToRightCons hole' right) cntx)) =      
  Just (Zipper hole' (CntxCons (ToLeftCons left hole) right cntx))        

-- Vzame/odstrani CntxCons it konteksta in z zipHole zgradi luknjo za star�evski kontekst
-- �e je kontekst prazen, ne moremo gor
-- �e gremo navzgor, moramo leve siblinge od luknje in desne siblige od luknje ter samo luknjo zdruziti, in to predstavlja novo 
-- luknjo, nov kontekts je pa parent kontekst od ternutnega konteksta. Kontekst vsebuje informacijo o levi in desnih siblingih, o 
-- luknji pa nima informacije, kajti ta je posebi predstavljena (prvi argument zipperja je luknja, drugi je kontekst z ToLeft in 
-- ToRight konstruktorji/verigami); ko gremo gor po zipperju, moramo zato, ker parent kontekst ne vsebuje informacije o luknji na 
-- njegovem nivoju (parent kontekst je shranjen znotraj trenutnega konteksta), sestaviti novo luknjo iz levih in desnih siblingov 
-- (prav tako shranjenih v kontekstu), nov kontekst je pa pac preprosto parent kontekst, ki pa vsebuje tudi leve in desne siblinge 
-- od nove, pravkar izracunane luknje
moveUp (Zipper _ CntxNull) = Nothing
moveUp (Zipper hole (CntxCons left right cntx)) =
  Just (Zipper (zipHole left hole right) cntx)
  
-- Pomo�na funkcija za pomik navzdol; ker nove vrednosti Context, ToLeft in ToRight �e en obstajajo pri pomiku navzdol, jih moramo 
-- pridobiti iztrenutne luknje z njeno 
-- dekonstrukcijo.
-- To nam omogo�a funkcija gfoldl, ki raz�leni konstruktor/funkcijo ne glede na njen tip (mora raz�irjati tip Data)
toLeft :: (Data leftArg) => leftArg -> ToLeft leftArg
toLeft leftArg = gfoldl ToLeftCons ToLeftUnit leftArg 

-- Z dekonstrukcijo luknje moramo ustvariti kontekst (Context) in sosednja vozli��a (Lefr in ToRight); ko gremo navzdol dobimo 
-- najbolj desni element trenutne luknje
-- Vstavimo/vrinemo luknjo v ToLeft konstrukt preko toLeft, zato ker luknja je neokrnjen podatek, torej �e ni zgrajena z ToLeft in 
-- ToRight, s tem pa luknjo razbijemo/zgradimo v/z ToLeft konstrukti
-- �e ne mores iti vec globlje, vrni Nothing
-- Vzamemo najbolj desni element (prvi levi znotraj luknje, torej prvi levi od "nove" luknje hole')
-- ko gremo navzdol, se vzame prvi element iz ToLeft construktorja/verige, torej je to najbolj desni, torej pridemo v najbolj desni 
-- element izraza/stare luknje
moveDown (Zipper hole cntx) =
  case toLeft hole of 
    ToLeftUnit _ -> Nothing 
    ToLeftCons left hole' -> 
      Just (Zipper hole' (CntxCons left ToRightNull cntx)) 
	  
-- PRETVORBA MED PODATKOVNIM TIPOM IN ZADRGO TEGA PODATKOVNEGA TIPA	  

-- Pretvorba iz podatkovnim tipom v zadrgo (ustvarjanje nove zadrge)
toZipper arg = Zipper arg CntxNull
toZipper :: (Data arg) => arg -> Zipper arg

-- Pretvorba iz zadrge nazaj v podatkovni tip.
-- Avtomatsko se premakne do samega korena zadrge in vrne korenski objekt ("odpet" izraz)
-- Pridobi korenski objekt zadrge/goli zacetni podatek, ki se ni bil razclenjen z konstrukti ToLeft, ToRight in Context (enako 
-- delovanje kot rekurzivno klicanje funkcije up, na koncu pa vrne luknjo (koren))
fromZipper :: Zipper arg -> arg
fromZipper (Zipper hole CntxNull) = hole
fromZipper (Zipper hole (CntxCons left right cntx)) =
  fromZipper (Zipper (zipHole left hole right) cntx)

-- FUNKCIJE ZA MANIPULACIJO LUKNJE.

-- genericna poizvedba (preoblikovanje/cast vrednosti)
-- pridobi vrednost trenutne luknje
query :: GenericQ gqfun -> Zipper z -> gqfun
query gqfun (Zipper hole cntx) = gqfun hole

-- genericna preslikava (zamenjava vrednosti)
-- preslikava/sprememba vrednosti trenutne luknje
trans :: GenericT -> Zipper z -> Zipper z
trans fun (Zipper hole cntx) = Zipper (fun hole) cntx

transM :: (Monad gmfun) => GenericM gmfun -> Zipper z -> gmfun (Zipper z)
transM gmfun (Zipper hole cntx) = do
  hole' <- gmfun hole
  return (Zipper hole' cntx)
  
-- Pridobi vsebino luknje (da ne rabmo sami klicati funkcije query direktno) in jo pretvori v tekst za prikaz
getHole :: (Typeable arg) => Zipper z -> Maybe arg
getHole = query cast

-- Spremeni vsebino luknje (da ne rabmo sami klicati funkcije trans direktno)
setHole :: (Typeable newArg) => newArg -> Zipper z -> Zipper z
setHole newArg z = trans (mkT (const newArg)) z
	 
-- PRIMER UPORABE

data Country = C President Institution
  deriving (Show, Typeable, Data)
data Institution = I Director [Subordinate] | Empty
  deriving (Show, Typeable, Data)
data Person = P Name Salary
  deriving (Show, Typeable, Data)
type President = Person
type Director = Person
type Subordinate = Person
type Salary = Float
type Name = String

country :: Country
country = C debevec institution

institution :: Institution
institution = I snoj [hren, kovac, vodopivec]

debevec, snoj, hren, kovac, vodopivec :: Person
debevec = P "Mirko Debevec" 7000
snoj = P "Janez Snoj" 5000
hren = P "Miha Hren" 3000
kovac = P "Venesa Kovac" 2000
vodopivec = P "Matjaz Vodopivec" 2000

-- h?_ spremenljivke je mozno izpisati
h0 = toZipper country
Just h1 = moveDown h0
Just h1_ = getHole h1 :: Maybe [Institution]
Just h2 = moveDown h1
Just h2_ = getHole h2 :: Maybe [Person]
Just h3 = moveLeft h2
Just h3_ = getHole h3 :: Maybe Person
Just h4 = moveDown h3
Just h4_ = getHole h4 :: Maybe Salary
Just h5 = moveLeft h4
Just h5_ = getHole h5 :: Maybe Name
h6 = setHole "Gospod Janez Snoj" h5
Just h7 = moveRight h6
h8 = setHole (10000 :: Float) h7
Just h9 = moveUp h8
Just h9_ = getHole h9 :: Maybe Person
Just h10 = moveUp h9
Just h10_ = getHole h10 :: Maybe [Institution]
Just h11 = moveUp h10
Just h11_ = getHole h11 :: Maybe Institution
Just h12 = moveUp h11
Just h12_ = getHole h12 :: Maybe Country
h13_ = fromZipper h8