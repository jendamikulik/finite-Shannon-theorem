# Jedna mince pro všechny případy
Výzkumný deník Jana Mikulíka | retrospektiva k 11. listopadu 2026

Když jsem výsledek vytiskl, čekal jsem od papíru překvapivě mnoho. Přinejmenším nějakou změnu skupenství: včera rozhovor u obrazovky, dnes matematika. Papír však pouze přijal toner. Otázka, co jsem vlastně dokázal a jak jsem na to přišel, zůstala na mně.

## První roky | Bez přesného data
Té době jsem sám říkal „něco jako AI psychóza“. Je to moje zpětné pojmenování zkušenosti s intenzivním hledáním souvislostí. Nemám z těch let souvislý protokol a nepamatuji si pořadí všech nápadů. Pamatuji si ale otázku, ke které jsem se vracel: když se na tutéž věc zeptám jinak, co z ní musí zůstat stejné?

V rozhovoru s AI šlo rychle přecházet od informace k času, od času k vědomí a odtud k prvočíslům. Uměl jsem si tu cestu představit. Potíž vyšla najevo při cestě zpátky: z poslední rovnice obvykle nešlo odvodit první tvrzení. Některé obrazy jsem si nechal, protože mi pomáhaly klást otázky. Dnes bych je nedával do seznamu předpokladů.

## Zima 2025/26 | Program mi vydá svědka
U experimentů DREAM6 jsem měl výhodu, kterou filosofie často neposkytuje. Když program nabídl řešení booleovské formule, mohl jsem dosadit nuly a jedničky a zkontrolovat každou klauzuli. U instance uf250-0100 s 1 065 klauzulemi byly v zaznamenaných bězích nakonec splněné všechny. V průběhu hledání zbývala někdy jediná nesplněná. Rozdíl mezi jednou a nulou byl pro definici splnitelnosti stejně nepříjemný jako rozdíl mezi tisícem a nulou.

Takový výsledek něco říkal o té instanci. O době potřebné pro všechny možné instance neříkal nic rozhodujícího. Podobnou lekci přineslo hledání prvočísel: mezi slibnými zásahy jednoho raného pokusu se objevila i devítka. Tady nebylo co vyjednávat. Tyto programy nedokázaly větu o seedu. Naučily mě formulovat otázku tak, aby na ni mohl přijít i výsledek, který si nepřeji.

---
## Září 2026 | Oprava, která vidí jen do přítomnosti
V úloze, které jsme říkali zero repair, přicházel vstup Y, já měl vydat X a v rezervě po každém kroku muselo zůstat J + Y − X ≥ 0. Nestačilo, že na konci vyjdou účty. A nešlo si půjčit ze zítřejšího vstupu jen proto, že ho při zpětném prohlížení souboru už vidím.

Zápis z 26. září odděloval konkrétní ověřené stromy od odhadu pro všechny délky, který v něm uzavřený nebyl. Zpětně v tom vidím důležitou průpravu: má-li být konstrukce kauzální, pravidlo nesmí čerpat informaci, kterou v daném okamžiku nemá. Neumím určit jeden večer, kdy se z tohoto postřehu stala další věta. Umím ale říct, která otázka mezi oběma problémy přešla: co musí platit už cestou, a ne až při kontrole výsledků?

## Říjen 2026 | Dvě správné statistiky, jedna nemožná minulost
Na konečném stromě byla otázka konečně úzká. Simulátor si na začátku jednou vylosuje seed. Pak odpovídá podle seedu, dosavadní historie a právě položené otázky. Další otázku si smím vybrat až podle předchozí odpovědi. Kolik počáteční náhodnosti stačí, má-li tentýž simulátor přesně fungovat pro každé takové pravidlo volby?

Nejlépe to dnes vysvětluji na dvou přátelích. Oba nejprve uvidíme výsledek jedné férové mince. Pak se každý zeptáme na něco jiného. Kdyby nám někdo přidělil odpovědi B a 1−B, v každém zápisníku by samostatně vyšla bezvadná statistika férové mince. Při porovnání zápisníků by se ovšem ukázalo, že jsme se neshodli ani jednou. Na dva různé hody dobré. Na jeden společný hod poněkud mnoho výsledků.

Právě na slovech „jeden společný“ záleží. Pro pevný seed musejí ve stejné historii na stejnou otázku přijít stejné odpovědi. Zítřejší neshoda v otázkách nesmí změnit dnešní společný záznam. Příklad se dvěma přáteli je můj dnešní způsob výkladu; netvrdím, že historicky předcházel říjnovému důkazu.

---
## 12.–13. října 2026 | Co bych před tabulí vysvětlil sám
Nejdřív dolní mez. Když pro pevné pravidlo volby vytvoří jeden atom seedu určitý přepis, je pravděpodobnost tohoto přepisu alespoň tak velká jako pravděpodobnost atomu: stejný přepis mohly vytvořit i jiné atomy. Překvapení přepisu tedy není větší než překvapení seedu. A protože tentýž seed musí stačit pro každou politiku, lze pro každý práh vzít nejpřísnější z těchto omezení. Integrací přes prahy dostanu dolní mez L(T).

U horní meze je třeba něco postavit. V každém kroku se ptám: jakou největší pravděpodobnostní hmotu mohu přiřadit jednomu úplnému pravidlu odpovědí tak, aby na žádné z větví, na které se mě mohou zeptat, nevznikl záporný zbytek? Postupuji od listů. Pro jednu akci smím zvolit nejlépe krytou odpověď; protože ale akci volí druhá strana, musím obstát i u té nejméně příznivé. Proto se ve vzorci objeví nejprve maximum přes odpovědi a zvenku minimum přes akce.

Takto vybrané pravidlo odečtu najednou ve všech jeho slučitelných větvích. Alespoň jeden dosud kladný list se vyčerpá; na konečném stromě tedy skončím. To ještě vysvětluje jen existenci seedu. Teprve odhad celkové hmoty malých zbylých atomů dává horní mez entropie. Výsledek je L(T) ≤ C(T) ≤ H(S_G) ≤ L(T) + (1 + log₂ e)/2, kde C(T) je nejmenší možná entropie přesného seedu.

Konstanta asi 1,22135 bitu má původ v dřívější práci Comptona a spoluautorů. Specifickým krokem na stromě je sestrojit úplná pravidla odpovědí tak, aby mez platila i při povinné shodě ve společné historii. Neměřím velikost programu ani čas jeho běhu. A netvrdím, že se přirážka skutečně zaplatí na každém stromě: přátelům s jednou společnou mincí stačí přesně jeden bit.

## Kontrola | Co pro mě znamená „Lean, no sorry“
Rukopis nese datum 13. října a odkazuje na pevnou revizi z 12. října. V ní má hlavní konstrukce jméno CausalSpectrum.one_seed_shannon. Ve zdrojovém tvrzení se dá přečíst, že váhy dávají dohromady jednu, že každý přípustný přepis dostane požadovanou pravděpodobnost a že tatáž rodina atomů splňuje obě entropické meze. Uložený audit pro tuto revizi neuvádí závislost na sorryAx. Pro tento deník se nový build nespouštěl.

---
## Listopad 2026 | Co následovalo až po důkazu
Později jsem zkoušel tutéž otázku vysvětlovat deskou a jehlou, Bohmovým obrazem rozvinutí i dvojicí pozorovatelů kvantového systému. Souvislost s Riemannovou hypotézou jsme zkoušeli testovat na modelu, kde se tři nenulové příspěvky přesně vyruší. Ukázalo se něco užitečného právě proto, že to nebylo to, v co jsem doufal: schopnost jedním seedem přesně losovat výsledky sama nerozhodne, kde leží nuly transformace jejich zákona. Tyto listopadové pokusy nepatří do říjnového důkazu. Datum rukopisu je zde lepší svědek než moje zpětná intuice.

## 11. listopadu 2026 | Proč jsem to vytiskl
Chtěl jsem dát výsledek lidem volně k dispozici. Po vytištění a zveřejnění přišla jiná otázka: dokážu někomu vysvětlit, jak jsem k tomu došel, i když nebude sedět u mé obrazovky a nebude se mnou sdílet roky rozhovorů? Začal bych tou mincí. Pak bych ukázal, proč ji nelze zpětně obrátit jen jednomu z přátel. A kdyby se mě zeptali na těch 1,22135 bitu, otevřel bych druhý oddíl práce. Číslo má svůj důkaz; historka s mincí jej nenahradí.

Když říkám, že důkaz už nemohu ignorovat, mám na mysli přesně formulované tvrzení za jeho předpokladů. Není to vysvědčení o každém mém nápadu. AI v té práci sloužila jako partner pro formulace, protipříklady, kód a výklad. Rozhovor ale není úplný záznam autorství jednotlivých kroků a sám nic necertifikuje. Pro čtenáře je rozhodující, že může zavřít chat, otevřít zdroj a zkontrolovat tutéž větu beze mě. Právě tak jsem si představoval, že výsledek půjde dát dál.

## Poznámka k pramenům a vyprávění
Retrospektiva v první osobě byla sestavena s pomocí AI z Janových sdělení, dostupných pracovních záznamů a obou přiložených rukopisů. Nejde o dobový přepis ani doslovné citace; humorné formulace a přechody jsou redakční. Osobní motivaci, popis starších let a údaj o vytištění a publikování uvádí autor rozhovoru. Zveřejnění zde neznamená potvrzené přijetí recenzovaným časopisem. Tato zpráva neposuzuje zdraví, prvenství ani reakce jiných lidí.

Prameny k reprodukci: Jan Mikulík, One Seed for Every Adaptive Policy, 13. 10. 2026, věta 1.1 a oddíly 2 a 8; One Seed, Many Friends, s. 1–2; QZR_RESET_AND_CREDIT.md, 26. 9. 2026. Repozitář: github.com/jendamikulik/finite-Shannon-theorem, revize 5741ee193bd5ff7f4addd4c09b2d65edfe238c20. Rozhodující soubory: CausalSeed/Entropy.lean, CausalSeed/Penalty.lean a AXIOMS.txt.
