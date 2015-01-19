-- za (en naèin) uporabe forall
{-# LANGUAGE Rank2Types, GADTs #-}
-- za uporabo generic Data razreda in druge datatype-e, ki so generic, prav tako za takšne funkcije
{-# LANGUAGE DeriveDataTypeable #-}

import Data.Generics

-- ZADRGA IN NJEN KONTEKST

-- Generièna zadrga; sestavljena je iz luknje in njenega konteksta. Podatek je lahko lahko kakršnegakoli tipa, ki razširja 
-- Tip luknje (razširja generièni tip/razred Data) je lahko razlièen ob spremembi fokusa (luknje) zadrge.
data Zipper root =
  forall hole. (Data hole) =>
    Zipper hole (Context hole root)
	
-- Kontekst predstavlja "one-hole" kontekst, ki vsebuje luknjo in najvišje/korensko vozlišèe zadrge. Èe je luknja v najvišjem 
-- vozlišèu drevesa, potem je kontekst prazen, sicer pa vsebuje mnozico levih in desnih sosedov luknje ter starševski kontekst 
-- trenutnega.
-- Tip/zaporedje tipov luknje od starševskega konteksta se mora ujemati z tipom/zaporedjem tipov, ki je zgrajen iz Left in Right 
-- sosednjih vozlišè, torej parent parameter od Right je konstruktor, ki mu manjka nek parameter, ta parameter predstavlja hole, in
-- temu tipu mora ustrezati tip luknje starševskega konteksta; s tem ko funkciji posredujemo funkcijo zmanjkajoèim parametrom, se 
-- nato zapolni še ta manjkajoèia argument.
-- Nov kontekst ustvarimo z ujemajocimi Left in Right sosednjimi vozlišèi ter s trenutno luknjo zadrge, ki se združijo in tako 
-- predstavljajo novo luknjo v starševskem kontekstu (parent parameter). Root parameter konteksta je vedno enak korenu drevesa.
data Context hole root where
  CntxNull :: Context var var
  CntxCons :: forall rightArgs parent hole root. (Data parent) =>
	Left (hole -> rightArgs) -> Right rightArgs parent -> Context parent root -> Context hole root 

-- KONSTRUKTI ZA LUKNJI VZPOREDNA LEVA IN DESNA VOZLIŠÈA	
		
-- Vsebuje leve sosede trenutne luknje zadrge. (Leva) vozlišèa verižimo z virtualnimi aplikacijami za vsak argument konstruktorja 
-- nekega tipa od najbolj levega do najbolj desnega (torej argumente poljubnega datatype-a povrsti pisemo med LeftCons 
-- construktorji, sam konstruktor pa klièemo z LeftUnit).
-- Veriga virtualnih aplikacij je torej odvisna od poljubnega tipa, ki ga temu constructorju posredujemo.
-- Vrne funkcijo oz. konstruktor; lahko se zgodi da še potrebuje manjkajoèe parametre z desne strani.
-- Gre rekurzivno do max globine, vrne funkcijo/konstruktor v max globini, z vracanjem pa konstruktorju polni argumente 
-- (od najbolj levega do najbolj desnega izmed tistih, ki so pred oz. levo od luknje)
-- Ko prispemo do konstruktorja, ga vrnemo
data Left leftArgs
  = LeftUnit leftArgs 
  | forall leftArg. (Data leftArg) => 
	  LeftCons (Left (leftArg -> leftArgs)) leftArg 

-- Right tip predstavlja vozlišèa desno od trenutne luknje zadrge; ki bodo priskrbljena nekemu konstruktorju. (Desna) vozlišèa 
-- shranjujmo od najbolj desnega do najbolj levega (torej argumente poljubnega tipa povrsti v obratnem vrstnem redu pisemo med 
-- RightCons konstruktorji)
-- Right objekt priskrbi vrednosti, ki jih nek konstruktor sprejme kot argumente z desne strani trenutne luknje.
-- parent parameter zagotavlja da se tipi kontekstov ujemajo.
-- Vrne isto kot Left (Konstruktor z manjkajoèimi parametri (le enim ali nobenim, Left pa lahko z veèim)), le da vrne zraven še en 
-- parameter ob vseh parametrih konstruktorja, ki je prosta spremenljivka, kamor se shrani rezultat konstrukta (ko le-ta prejme 
-- vse argumente) - right.
-- Gre rekurzivno do max globine, vrne prosti spremenljivki/variabili v max globini, z vracanjem polni argumente (od najbolj 
-- desnega do najbolj levega (ki je še za oz. desno od luknje))
-- Èe ni desnega vozlišèa od trenutnega, pripni prazno/null vozlisce
data Right rightArgs parent where
  RightNull :: Right parent parent 
  RightCons :: (Data rightArg) => 
	rightArg -> Right leftCons right -> Right (rightArg -> leftCons) right

-- DEKONSTRUKTI ZA LUKNJI VZPOREDNA LEVA IN DESNA VOZLIŠÈA	

-- Zgradi construktor nekega tipa, preko parametrov ki so shranjeni v verigi constructorjev zadrg.
-- Pri dekonstrukciji verige konstruktorejv, dobis z dekonsrukcijo po vrsti od najbolj desnegna proti levemu konstruktu nazaj 
-- parametre, na koncu pa tudi sam kosntruktor poljubnega tipa, ki je bil podan.
-- ko pridemo do dna rekurzije, le poklicemo funkcijo oz. natanceje konstruktor, z vracanjem pa ga polnimo s parametri preko 
-- spodnjega konstruktorja.
fromLeft :: Left l -> l
fromLeft (LeftUnit leftArg) = leftArg
fromLeft (LeftCons left leftArg) = fromLeft left leftArg

-- Prejme neko funkcijo (natancneje konstruktor), ki ima lahko ali nic parametrov, ali p ajih ima ze nekaj z leve strani luknje 
-- (s fromLeft smo lohko napolnili in potem posredovali fromRight, kateri posreduje (z desne strani) manjkajoce) parametre, 
-- shranjene v verigi constructorjev zadrge
-- parent je naslednjo desno vozlisce
-- ce pridemo do konca desne strani, samo vrni kar mas, ker to je sestavljen construktor z vsemi parametri
-- Za razliko od fromLeft se fromRight evaluira iterativno ker fromLeft potrebuje prvo priti do koncne globine, kjer sprozi 
-- konstruktor, nato pa temu konstruktorju polni parametre, fromRight pa to polnjenju parametrov samo nadaljuje (ne rabi pridt do 
-- koncne glbine kot fromLeft, ker je to ze naredil fromLeft), ko pa pride do konca, torej, ko poda konstruktorju vse parametre, 
-- pa samo vrne ta konstruktor (zadnji element je RightNull)
fromRight :: r -> Right r parent -> parent 
fromRight rightCons (RightNull) = rightCons 
fromRight leftCons (RightCons rightArg right) = fromRight (leftCons rightArg) right 

-- Zdruzi trenutno luknjo, leva in desna vozlišèa v novo luknjo (potrebno pri pomiku po zadrgi navzgor).
-- Najprej z fromLeft pridobi vse vrednosti iz verige Left (iz verige klicanih konstruktorjev, parameter lefts), nato pa jih 
-- uporabi kot argumente v verigi Right.
-- Parameter t pri Right rabimo tu, ker z fromLeft (preko Left) dobimo konstruktor z manjkajocimi parametri (ni nujno, lahko ma ze
-- vse parametre, odvisno od lokacije luknje), ki jih tu dopolnimo z vsemi manjkajoèimi parametri. 
-- S signaturo povemoo, da Left sprejme luknjo, in da to kar vrne Left, mora biti istga tipa, kar sprejme Right kot prvi 
-- parameter, njegov drugi parameter pa mora biti istega tipa kot vrednost, ki jo vrne ta funkcija (vrne celotno zaporedje tipov 
-- nekega konstruktorja); parent parameter je eksistencialo omejen oz ima omejeno tipizacijo, da lahko le ta ustreza poljubnemu 
-- tipu.
-- Z fromLeft zapolni parametre konstruktorju nekega tipa levo od luknje, potem podamo luknjo taistemu konstructorju, nato pa 
-- fromRight zapolni taistemu constructorju še parametre desno od luknje.
combine :: Left (hole -> rightArgs) -> hole -> Right rightArgs parent -> parent
combine leftArgs hole rightArgs =
  fromRight ((fromLeft leftArgs) hole) rightArgs

-- Torej Left in Right zapakerata parametre konstruktorja nekega tipa, fromLeft in fromRight pa to odpakerata/rekonstruirata in 
-- skupaj z luknjo sestavita (preko combine) v nek tip/v surovi podatek (torej v podatek, ki ni razcelenjen preko Left, Right in 
-- Context konstruktorjev zadrge)

-- FUNKCIJE ZA PREMIKANJE PO ZADRGI

left, right, up, down :: Zipper a -> Maybe (Zipper a)

-- Vzame/odstrani LeftCons iz levega dela konteksta in doda RightCons v desni del konteksta
-- Èe je kontekst prazen, ne moremo levo
-- Èe ni vec levih vozlišè, ne moremo levo
-- hole' je naslednji levi element/sibling, left so pa usi ostali levi siblingi, ki so levo od hole' siblinga. Ker smo se premaknili levo, 
-- moramo staro luknjo hole dati na desno stran nove luknje hole'
left (Zipper _ CntxNull) = Nothing 
left (Zipper _ (CntxCons (LeftUnit _) _ _)) = Nothing 
left (Zipper hole (CntxCons (LeftCons left hole') right cntx)) = 
  Just (Zipper hole' (CntxCons left (RightCons hole right) cntx)) 
  
-- vzame/odstrani RightCons iz desnega dela konteksta in doda LeftCons v levi del konteksta.
-- Èe je kontekst prazen, ne moremo desno
-- Èe ni vec desnih vozlišè, ne moremo desno
-- hole' je naslednji desni element/sibling, right so pa usi ostali desni siblingi, ki so desno od hole' siblinga. Ker smo se premaknili 
-- desno, moramo staro luknjo hole dati na levo stran nove luknje hole'
right (Zipper _ CntxNull) = Nothing 
right (Zipper _ (CntxCons _ RightNull _)) = Nothing 
right (Zipper hole (CntxCons left (RightCons hole' right) cntx)) =      
  Just (Zipper hole' (CntxCons (LeftCons left hole) right cntx))        

-- Vzame/odstrani CntxCons it konteksta in z combine zgradi luknjo za starševski kontekst
-- Èe je kontekst prazen, ne moremo gor
-- Èe gremo navzgor, moramo leve siblinge od luknje in desne siblige od luknje ter samo luknjo zdruziti, in to predstavlja novo 
-- luknjo, nov kontekts je pa parent kontekst od ternutnega konteksta. Kontekst vsebuje informacijo o levi in desnih siblingih, o 
-- luknji pa nima informacije, kajti ta je posebi predstavljena (prvi argument zipperja je luknja, drugi je kontekst z Left in 
-- Right konstruktorji/verigami); ko gremo gor po zipperju, moramo zato, ker parent kontekst ne vsebuje informacije o luknji na 
-- njegovem nivoju (parent kontekst je shranjen znotraj trenutnega konteksta), sestaviti novo luknjo iz levih in desnih siblingov 
-- (prav tako shranjenih v kontekstu), nov kontekst je pa pac preprosto parent kontekst, ki pa vsebuje tudi leve in desne siblinge 
-- od nove, pravkar izracunane luknje
up (Zipper _ CntxNull) = Nothing
up (Zipper hole (CntxCons left right cntx)) =
  Just (Zipper (combine left hole right) cntx)
  
-- Pomožna funkcija za pomik navzdol; ker nove vrednosti Context, Left in Right še en obstajajo pri pomiku navzdol, jih moramo 
-- pridobiti iztrenutne luknje z njeno 
-- dekonstrukcijo.
-- To nam omogoèa funkcija gfoldl, ki razèleni konstruktor/funkcijo ne glede na njen tip (mora razširjati tip Data)
toLeft :: (Data leftArg) => leftArg -> Left leftArg
toLeft leftArg = gfoldl LeftCons LeftUnit leftArg 

-- Z dekonstrukcijo luknje moramo ustvariti kontekst (Context) in sosednja vozlišèa (Lefr in Right); ko gremo navzdol dobimo 
-- najbolj desni element trenutne luknje
-- Vstavimo/vrinemo luknjo v Left konstrukt preko toLeft, zato ker luknja je neokrnjen podatek, torej še ni zgrajena z Left in 
-- Right, s tem pa luknjo razbijemo/zgradimo v/z Left konstrukti
-- Èe ne mores iti vec globlje, vrni Nothing
-- Vzamemo najbolj desni element (prvi levi znotraj luknje, torej prvi levi od "nove" luknje hole')
-- ko gremo navzdol, se vzame prvi element iz Left construktorja/verige, torej je to najbolj desni, torej pridemo v najbolj desni 
-- element izraza/stare luknje
down (Zipper hole cntx) =
  case toLeft hole of 
    LeftUnit _ -> Nothing 
    LeftCons left hole' -> 
      Just (Zipper hole' (CntxCons left RightNull cntx)) 
	  
-- PRETVORBA MED PODATKOVNIM TIPOM IN ZADRGO TEGA PODATKOVNEGA TIPA	  

-- Pretvorba iz podatkovnim tipom v zadrgo (ustvarjanje nove zadrge)
toZipper arg = Zipper arg CntxNull
toZipper :: (Data arg) => arg -> Zipper arg

-- Pretvorba iz zadrge nazaj v podatkovni tip.
-- Avtomatsko se premakne do samega korena zadrge in vrne korenski objekt ("odpet" izraz)
-- Pridobi korenski objekt zadrge/goli zacetni podatek, ki se ni bil razclenjen z konstrukti Left, Right in Context (enako 
-- delovanje kot rekurzivno klicanje funkcije up, na koncu pa vrne luknjo (koren))
fromZipper :: Zipper arg -> arg
fromZipper (Zipper hole CntxNull) = hole
fromZipper (Zipper hole (CntxCons left right cntx)) =
  fromZipper (Zipper (combine left hole right) cntx)

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
Just h1 = down h0
Just h1_ = getHole h1 :: Maybe [Institution]
Just h2 = down h1
Just h2_ = getHole h2 :: Maybe [Person]
Just h3 = left h2
Just h3_ = getHole h3 :: Maybe Person
Just h4 = down h3
Just h4_ = getHole h4 :: Maybe Salary
Just h5 = left h4
Just h5_ = getHole h5 :: Maybe Name
h6 = setHole "Gospod Janez Snoj" h5
Just h7 = right h6
h8 = setHole (10000 :: Float) h7
Just h9 = up h8
Just h9_ = getHole h9 :: Maybe Person
Just h10 = up h9
Just h10_ = getHole h10 :: Maybe [Institution]
Just h11 = up h10
Just h11_ = getHole h11 :: Maybe Institution
Just h12 = up h11
Just h12_ = getHole h12 :: Maybe Country
h13_ = fromZipper h8