# Exact causal seeds on controlled trees

Machine-checked statements about one shared random seed that realizes every deterministic policy law on a controlled tree.

**Jan Mikulik — October 2026**

A deterministic policy chooses the next action from the observed history. A response strategy is stronger: at every history it names an output for every available action, including actions the realized path does not take. A causal seed is one probability law on such total strategies. The same draw must reproduce the prescribed transcript law of every deterministic policy. An ordinary coupling of those laws need not be consistent on shared histories. A causal seed must be.

The finite theorem is

> **Z ≼st J ≼st Z + E**, with **E ~ Exp(ln 2)**,

and therefore

> **L(T) ≤ H(S) ≤ L(T) + c\***, **c\* = (1 + log₂ e) / 2 ≈ 1.2213475204 bits.**

`L(T)` is the envelope mean `envelopeMean T`. The additive constant does not depend on the depth of the finite tree. The stochastic comparison alone gives the weaker constant `log₂ e`; the refined greedy cutoff improves it to `c*`.

Only declarations in the Lean development are results of this repository. `AXIOMS.txt` records `#print axioms` for the principal finite theorems and for the infinite-horizon results through the envelope bridge, from the build of 11 October 2026 (Lean 4.35.0-rc3, mathlib `7d6757bc18680044fc0ff6efc8ee20494b408556`). Those declarations depend only on `propext`, `Classical.choice` and `Quot.sound`. The audited files contain no `sorry` and no `admit`.

---

## Finite realization

`T` is a finite controlled history tree. Every nonterminal history has a finite nonempty action set; every action has a finite nonempty output alphabet; the transition probabilities are strictly positive and sum to one.

```text
CausalSpectrum.causal_realization
```

builds one finite seed by greedy extraction of the probability flow. For every deterministic policy `π` and every compatible transcript `ℓ`,

> **P[run(S, π) = ℓ] = p_T(ℓ).**

Incompatible transcripts get mass zero. The seed is drawn once, not once per policy.

If `J` is the information of a seed atom and `Z` is the information variable of the lower envelope of the policy transcript laws, the two stochastic comparisons are, for every real `t`,

```text
seedCDF t  ≤ Fstar T t
seedTail t ≤ coupleSurv T t
```

```text
CausalSpectrum.one_seed_shannon
```

integrates them to `L(T) ≤ H(S) ≤ L(T) + c*`. The same seed satisfies the operational tail bound

> **P(J > t + s) ≤ P(Z > t) + 2^−ˢ** for `s ≥ 0`,

which is `CausalSpectrum.causal_truncation`.

---

## Ordinary couplings and the penalty identity

Write `C(T)` for the causal entropy optimum and `G*` for the universal causal gap `gapSup`.

```text
CausalSpectrum.gapSup_le_shannonOverhead
```

proves `G* ≤ c*`. It does not evaluate `G*`. The checked lower bound is only

> **2/9 ≤ G***,

from `CausalSpectrum.witness_gapSup_lower`: an ordinary coupling of profile `(3,2,2,1,1)/9` against a causal lower bound of profile `(3,2,1,1,1,1)/9`. That witness does not identify either optimum with its profile.

For every coefficient `κ ≥ G*`,

> **C(T) = inf_Γ [ H(Γ) + κ · Γ(B) ]**,

where `B` is the incompatible part of the coupling. The identity is

```text
CausalSpectrum.penaltyMin_eq_causalMin
CausalSpectrum.causalMin_le_penalised
```

with the shortfall form `CausalSpectrum.penalty_shortfall`.

---

## Infinite trees: atomic capacity

The infinite objects are locally finite controlled trees. Exactness means agreement on every finite cylinder.

Finite greedy seeds have ordered weights. A diagonal limit produces strategy atoms. `atomQ` is the total mass of that limit. The development then builds three objects.

1. `atomMeasure`, of total mass `atomQ`, with cylinder mass `cylMass h`.
2. `residualMeasure`, the infinite product of the residual kernels. Where the residual mass vanishes, the kernel falls back to the original transition, so the ratios sum to one on every action.
3. `fullMeasure`, the mixture. It is a probability, and the cylinder of a finite history `h` has mass `pathMass h`.

The cylinder identity, already at the level of real functions, is

> **cylMass(h) + resMass(∅) · resCyl(h) = pathMass(h).**

An ordinary exact source may use a separate measurable readout for each finite policy. No causal agreement between those readouts is assumed. Nevertheless its atomic mass is at most `atomQ`, and `fullMeasure` attains that value. A countably supported exact causal seed exists if and only if `atomQ = 1`; in that case the atomic measure itself is exact.

```text
CausalSpectrum.Completion.ordinary_atomic_upper
CausalSpectrum.Completion.causal_atomic_capacity_attained
CausalSpectrum.Completion.countable_seed_iff_atomQ_one
CausalSpectrum.Completion.discrete_seed_of_atomQ_one
CausalSpectrum.Completion.fullMeasure_cylinder
CausalSpectrum.exact_split
```

`atomQ = lim F_∞` is not a theorem.

The finite input to the diagonal limit is the greedy concentration estimate. If every policy puts mass at least `a` on some `K` transcripts, the first `M` greedy weights satisfy

> **∑_{i < M} w_i ≥ a · (1 − (1 − 1/K)^M).**

This is `CausalSpectrum.greedy_head_lower`. The same prefix is at most the mass of the `M` most likely transcripts of every policy: `CausalSpectrum.greedy_prefix_le_topMass`.

---

## Projective entropy and the envelope bridge

Entropy of a countable seed is the extended Shannon sum in nats (`Real.negMulLog`). A ranked seed is the same data with nonincreasing weights. Ranking is free: every countable seed has a ranked rearrangement that preserves total mass, every cylinder sum, the induced measure, the entropy, and exactness at each finite horizon and at infinity.

```text
CausalSpectrum.Completion.CountableSeed.exists_ranked
CausalSpectrum.Completion.finiteCost_eq_countable
CausalSpectrum.Completion.infiniteCost_eq_countable
```

Let `C_n` be the infimum of entropy over countable seeds exact through horizon `n`, and let `C_∞` be the infimum over seeds exact at every finite horizon. Both may be infinite. Then

> **C_∞ = sup_n C_n.**

This is `CausalSpectrum.Completion.projective_entropy_identity`. If the supremum is finite, a ranked seed attains it (`entropy_attained`), and then `atomQ = 1`.

Let `L_∞ = sup_n L(T_n)` in bits, where `T_n` is the horizon-`n` truncation. Converting units by `nats = (ln 2) · bits`,

> **(ln 2) · L_∞ ≤ C_∞ ≤ (ln 2) · (L_∞ + c\*).**

Hence `C_∞ < ∞` if and only if `L_∞ < ∞`. A finite-entropy exact countable seed exists exactly when the finite envelope means stay uniformly bounded.

```text
CausalSpectrum.Completion.infiniteCost_bridge
CausalSpectrum.Completion.infiniteCost_lt_top_iff
```

The comparison does not identify `G*`.

---

## Arithmetic rigidity

These statements do not use the Shannon bound.

For a fixed positive finite weight vector, the incompatible mass of an exact decoder family is the total weight of atoms that participate in a subset-sum collision. Every exact decoder family on every finite controlled tree is causally realizable if and only if all subset sums are distinct. For uniform marginal error `ε`, collisions are replaced by subset sums at distance at most `2ε`, and the sharp universal threshold is `2ε < gamma`. The obstruction is attained on a controlled tree of depth at most two.

```text
CausalSpectrum.exact_rigidity
CausalSpectrum.sharp_threshold
CausalSpectrum.profile_attainment
CausalSpectrum.bad_mem_defect
CausalSpectrum.unrealizable_splits
```

If each policy may apply its own weight-preserving permutation of the seed, causal repair is equivalent to count-stability of the weights, and the sharp threshold is stated in terms of `deltaRel`.

```text
CausalSpectrum.relabelRepair_iff_countStable
CausalSpectrum.sharp_relabel
CausalSpectrum.repair_same_law
```

---

## Second-order asymptotics for a stationary kernel

`CausalSeed/Sqrt*.lean` treats a kernel that is the same at every history, with a common binary entropy `h` on every action (`Kernel.EqualEntropy`). Write `a` and `b` for the largest and least standard deviation of the centered surprisal increments. The second-order coefficient in the development is

> **√(2/π) · (a − b).**

For the horizon-`n` truncation, `SqrtGeneral.lean` proves the normalized limit

> **(L_n − n h) / √n → √(2/π) · (a − b)**,

and the same limit for the optimal exact seed entropy `C_n`, measured in bits.

```text
CausalSpectrum.Kernel.envelope_tendsto
CausalSpectrum.Kernel.cost_tendsto
```

The case `b = 0` is included, by a variance perturbation; if `a = b = 0` the coefficient is zero. When `b > 0`, `SqrtMain.lean` gives a rate: for every `n ≥ 3`,

> **|L_n − n h − √(2/π)(a − b) √n| ≤ K · n^{1/4} log n**,

and the same bound for `C_n` and for the entropy of a greedy seed furnished by `one_seed_shannon`.

```text
CausalSpectrum.Kernel.envelope_rate
CausalSpectrum.Kernel.cost_rate
CausalSpectrum.Kernel.greedy_rate
```

The bridge from the Bellman envelope of centered surprisals back to `envelopeMean` is `Kernel.mean_identity` in `SqrtBridge.lean`. This asymptotic does not evaluate `G*`, and it is not a statement about a tree whose kernel changes with the history.

These modules are in the import closure of `CausalSeed/Main.lean`. `AXIOMS.txt` does not yet record a separate `#print axioms` pass for them.

---

## What the axiom audit covers

Recorded in `AXIOMS.txt`, build of 11 October 2026, and the earlier finite audits of 8 and 10 October:

| Declaration | Statement |
| --- | --- |
| `causal_realization` | One exact finite causal seed, with the exponential stochastic comparison |
| `one_seed_shannon` | `L(T) ≤ H(S) ≤ L(T) + c*` |
| `causal_truncation` | Uniform tail bound on the same seed |
| `penaltyMin_eq_causalMin` | Exact penalty representation for every `κ ≥ G*` |
| `gapSup_le_shannonOverhead` | `G* ≤ c*` |
| `witness_gapSup_lower` | `2/9 ≤ G*`, and nothing sharper |
| `exact_rigidity`, `sharp_threshold` | Subset sums characterize exact causal realizability |
| `relabelRepair_iff_countStable` | Weight-preserving relabeling |
| `greedy_head_lower` | Concentration of the first `M` greedy weights |
| `Completion.causal_atomic_capacity_attained` | Ordinary and causal atomic capacity both equal `atomQ`, and the causal value is attained |
| `Completion.countable_seed_iff_atomQ_one` | A countable exact seed exists ⇔ `atomQ = 1` |
| `Completion.projective_entropy_identity` | `C_∞ = sup_n C_n` for ranked seeds, entropy in nats |
| `Completion.infiniteCost_bridge` | `(ln 2) · L_∞ ≤ C_∞ ≤ (ln 2) · (L_∞ + c*)` |

The following files are imported, and they contain the declarations named in their headers, but those headers still say the files were not locally compiled, and `AXIOMS.txt` does not audit them. They are not listed above as checked results.

| File | What the source states |
| --- | --- |
| `StrictPenalty.lean` | For `κ > G*`, an attained penalty minimizer is causal |
| `SeedDataProcessing.lean` | Push-forward does not raise entropy; finite envelope lower bound |
| `FiniteSeedExtension.lean` | A finite exact seed extends to an infinite seed, exact up to that horizon |
| `AlphabetSeed.lean`, `CountableAlphabet.lean` | A seed on an arbitrary countable alphabet ranks onto `ℕ` without changing entropy or cylinder sums |
| `InfiniteEnvelope.lean` | The same `L_∞` sandwich, packaged as `infiniteEnvelope` |

`InfiniteEnvelope.lean` restates a comparison already audited as `infiniteCost_bridge`. It is not an independent strengthening.

Not theorems, in the audited development or outside it:

- the exact value of `G*`;
- `atomQ = lim F_∞`;
- a theorem for a branch of probability zero, unless that branch is removed or the statement is rewritten;
- any claim that a minimizer at the endpoint `κ = G*` is compatible. The strict statement lives only in the unaudited file `StrictPenalty.lean`.

---

## Repository map

| Path | Role |
| --- | --- |
| `CausalSeed/Spectrum.lean` | Trees, policies, strategies, minimax, greedy extraction |
| `CausalSeed/Entropy.lean` | Finite realization and the Shannon bound |
| `CausalSeed/Gap.lean` | Envelope versus an ordinary coupling |
| `CausalSeed/Penalty.lean` | The gap `G*` and the penalty |
| `CausalSeed/Close.lean` | Removal of the compatible part |
| `CausalSeed/Transport.lean` | Residual transport on the pruned tree |
| `CausalSeed/Identity.lean` | The penalty identity |
| `CausalSeed/Witness.lean` | The lower bound `2/9 ≤ G*` |
| `CausalSeed/Arithmetic.lean`, `Probe.lean`, `Profile.lean` | Subset sums, the defect, depth-two attainment |
| `CausalSeed/Relabel.lean` | Relabeling repair |
| `CausalSeed/Atomic.lean` | Greedy concentration and `diagMass = atomQ` |
| `CausalSeed/Capacity.lean` | Residual kernels and `exact_split` |
| `CausalSeed/MeasureCompletion.lean` | Atomic measure, residual product, exact mixture |
| `CausalSeed/AtomicCapacity.lean` | Ordinary upper bound and causal attainment |
| `CausalSeed/EntropyLimit.lean` | `C_∞ = sup_n C_n` and attainment |
| `CausalSeed/SeedRanking.lean` | Ranked rearrangement |
| `CausalSeed/EnvelopeBridge.lean` | The bridge from `C_∞` to `L_∞` |
| `CausalSeed/Bellman.lean`, `BellmanCompare.lean` | The discrete Bellman envelope |
| `CausalSeed/SqrtProfile.lean` through `SqrtGeneral.lean` | Second-order profile, rate, and the general limit |
| `CausalSeed/SecondOrder.lean` | Integral identities used by the profile |
| `AXIOMS.txt` | The recorded axiom audit |

`CausalSeed.lean` imports the development.

---

## Build

The toolchain is pinned by `lean-toolchain`, `lake-manifest.json` and `lakefile.toml`.

```bash
lake build
```

A declaration is a machine-checked result of this repository only after it is accepted by that build. The axiom audit for the declarations in the table above is the text of `AXIOMS.txt`, not this README.

---

## Status of the ideas

This repository does not claim originality, priority, or independence from prior mathematics.

It is not known, and it is not decided here, whether a formulation in these sources is an original argument, a reconstruction of existing mathematics, or a recombination of material on which a language model was trained, including work by other people. No attempt is made to tell those cases apart.

Nothing of that kind is claimed. The only thing this repository does is validate: a statement that the Lean kernel accepts, under the axioms recorded for it, is a checked statement. Validation is not attribution. If a theorem recorded here already belongs to someone else, the credit belongs to them.
