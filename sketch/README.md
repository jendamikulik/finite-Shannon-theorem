# Náčrt: otázky, struktura, kauzální simulace

Stav: **neověřený náčrt**. Není součástí knihovny `CausalSeed`, není importovaný z `Main.lean` a nebyl tu spuštěný `lake build`. Certifikát z toho bude až po úspěšném

```sh
lake env lean sketch/QuestionsStructure.lean
```

na `leanprover/lean4:v4.35.0-rc3` s připnutým mathlibem.

Zdroj: [`questions_structure_causal_simulation.pdf`](../questions_structure_causal_simulation.pdf).

## Co soubor dělá

`sketch/QuestionsStructure.lean` formalizuje elementární kostru té poznámky:

- otázky dávají injektivní faktor na obraz; víc otázek kvocient jemňí;
- prázdná sada otázek na neprázdné Ω dá jednu třídu, ne nulu stavů;
- budoucí pozorování dávají největší kongruenci a kvocient, který přepisy reprodukuje;
- současná odpověď na to nestačí (příklad se třemi stavy);
- dosažení zachová invarianty; univerzální dosažitelnost je nutí být konstantní;
- konstantní invarianty nestačí na univerzální dosažitelnost;
- přesný výběr cíle z `Fin n` potřebuje aspoň `n` řídicích hodnot na jedno semínko;
- z prázdné množiny vede jediná funkce a nic nezobrazí; z jednoprvkové vede právě výběr prvku;
- na dvouprvkové množině není bod pevný všemi bijekcemi;
- generování z prázdného startu zůstane prázdné; skryté rozšíření nemění pozorovatelný běh.

## Co v souboru není

- stochastická lumpabilita a rovnost cen semínka (věta 4.1);
- Fanova nerovnost pro entropii výběru (věta 6.1); je jen nosičový odhad `n ≤ k`;
- mez `m - 1` na počet zjemnění;
- entropie symetrického semínka `log₂ N` a spočetný případ bez invariantní míry.

## Popisek

Otázka bez budoucího uzávěru nedá přechod. Přesný kvocient zachová přepisy, ne skrytý stav. Dosažitelnost není výběr: výběr nese informaci v řízení. Prázdný vstup, zadaný bod a symetrie jsou tři různé věci. Žádná z nich nevyrábí invariant, který v zadání nebyl.
