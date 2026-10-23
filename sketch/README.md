# Náčrt: otázky, struktura, kauzální simulace

Stav: oba soubory prošly `lake env lean` na `leanprover/lean4:v4.35.0-rc3` s mathlibem `7d6757bc18680044fc0ff6efc8ee20494b408556`.

Pořád nejsou součást knihovny `CausalSeed`, nejsou importované z `Main.lean` a nejsou to rozšíření certifikátu o ceně semínka.

## Soubory

- `sketch/QuestionsStructure.lean` — elementární kostra poznámky o otázkách a kauzální simulaci.
- `sketch/RelativeRest.lean` — relativní klid. Věta 1 (přesná redukce), tři významy klidu, Věta 2, živá skrytá souřadnice, Věta 3, krabice `F`/`R`, nosičový skok ceny a nosičová forma výběru.

Není tam Shannonova entropie, stochastická lumpabilita ani `Cₙ` jako entropické infimum.

## Popisek

Pozorovatelný klid je vlastnost trojice stav, pozorování, přípustné zásahy. Skrytá souřadnice pod ním může žít. Nový zásah ekvivalenci zjemní. Nosičově: zmrzlý transkript unese jednobodové semínko, odkrytí skrytého bitu ne.
