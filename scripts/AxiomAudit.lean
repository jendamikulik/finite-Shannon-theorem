/-
Axiom audit of every theorem declared in the project's own modules (`CausalSeed.*`).
Run from the repository root after `lake build`:

    lake env lean scripts/AxiomAudit.lean > axioms_audit.out

Prints one line per theorem: `<module> <name> : [axioms]`, then a summary.
Auto-generated declarations (internal names, `_proof_`, `match_`, equation lemmas, ...)
are excluded.
-/
import CausalSeed.Main
open Lean Elab Command

run_cmd do
  let env ← getEnv
  let mut rows : Array (Name × Name × Array Name) := #[]
  let mut projAxioms : Array Name := #[]
  for (n, ci) in env.constants.toList do
    let some idx := env.getModuleIdxFor? n | continue
    let mod := env.header.moduleNames[idx.toNat]!
    unless (`CausalSeed).isPrefixOf mod do continue
    if ci matches .axiomInfo _ then projAxioms := projAxioms.push n
    unless ci matches .thmInfo _ do continue
    if n.isInternalDetail || isAuxRecursor env n || isNoConfusion env n then continue
    if (← liftCoreM (Meta.isMatcher n)) then continue
    let last := n.components.getLast!.toString
    if last.startsWith "eq_" || last == "eq_def" || last.startsWith "_" then continue
    if ["sizeOf_spec", "inj", "injEq", "eq"].contains last then continue
    if n.components.any (fun c => ["brecOn", "binductionOn", "below"].contains c.toString) then continue
    if (← liftCoreM (Meta.isInstance n)) then continue
    let axs ← liftCoreM (collectAxioms n)
    rows := rows.push (mod, n, axs.qsort (·.lt ·))
  rows := rows.qsort (fun a b => a.1.lt b.1 || (a.1 == b.1 && a.2.1.lt b.2.1))
  let std : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut nAx : Nat := 0
  let mut nonstd : Array Name := #[]
  for (mod, n, axs) in rows do
    logInfo m!"{mod} {n} : {axs.toList}"
    if axs.isEmpty then nAx := nAx + 1
    if axs.any (fun a => !std.contains a) then nonstd := nonstd.push n
  logInfo m!"TOTAL {rows.size} theorems; {nAx} depend on no axioms; non-standard: {nonstd.toList}; axioms declared in CausalSeed: {projAxioms.toList}"
