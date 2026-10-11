# Exact causal seeds on controlled trees

### Machine-checked finite and infinite-horizon results for shared randomness in controlled stochastic processes

**Jan Mikulik — October 2026**

This repository studies the following problem.

A single random seed chooses a **total response strategy**. Every deterministic adaptive policy must then obtain the prescribed stochastic law from that same seed.

The central finite result is:

> **Z ≼ₛₜ J ≼ₛₜ Z + E, where E ~ Exp(ln 2).**

The corresponding entropy bound is:

> **L(T) ≤ H(S) ≤ L(T) + c\***  
> **c\* = (1 + log₂ e) / 2 ≈ 1.2213475204 bits.**

The same seed is exact for **every deterministic adaptive policy on the tree**.

The development is formalized in Lean and contains no `sorry` or `admit`.

---

## Main result

Let `T` be a finite controlled history tree.

At every nonterminal history:

- the action set is finite and nonempty;
- every action has a finite nonempty output alphabet;
- the corresponding transition probabilities are strictly positive and sum to one.

A deterministic policy chooses an action from the observed history.

A deterministic response strategy is a stronger object: it specifies an output for every available action at every history, including actions that are not taken along a particular realized path.

A causal seed is a probability distribution over such total strategies.

The distinction is essential. An ordinary coupling only has to reproduce the individual policy laws. A causal seed must reproduce them using one shared strategy structure that is consistent at common histories.

### Exact realization

The declaration

```text
CausalSpectrum.causal_realization
```

constructs one finite seed by greedy extraction of the probability flow.

For every deterministic policy `π` and every compatible transcript `ℓ`,

> **P[run(S, π) = ℓ] = p_T(ℓ).**

Incompatible transcripts receive probability zero.

The seed is chosen once. It is not chosen separately for each policy.

If

- `J` is the information content of a seed atom, and
- `Z` is the information variable associated with the lower envelope of the deterministic-policy transcript laws,

then

> **Z ≼ₛₜ J ≼ₛₜ Z + E**,  
> where **E ~ Exp(ln 2)**.

In Lean, the two comparisons are represented by

```text
seedCDF t  ≤ Fstar T t
seedTail t ≤ coupleSurv T t
```

for every real `t`.

---

## Shannon bound

The declaration

```text
CausalSpectrum.one_seed_shannon
```

proves

> **L(T) ≤ H(S) ≤ L(T) + c\***

with

> **c\* = (1 + log₂ e) / 2 ≈ 1.2213475204 bits.**

Here `L(T)` is `envelopeMean T`.

The lower bound comes from the envelope.

The upper bound uses the refined greedy cutoff estimate. The stochastic exponential comparison alone gives the weaker additive constant `log₂ e`; the refinement improves this to `c*`.

The additive constant is independent of the depth of the finite tree.

---

## Uniform truncation

The same seed satisfies

> **P(J > t + s) ≤ P(Z > t) + 2⁻ˢ**, for `s ≥ 0`.

This is

```text
CausalSpectrum.causal_truncation
```

and is an operational consequence of the same causal realization.

---

## Ordinary coupling and causal compatibility

An ordinary coupling of policy transcript laws need not be consistent at shared histories.

A causal seed must be.

Let

- `M(T)` be the ordinary coupling optimum;
- `C(T)` be the causal optimum;
- `G*` be the universal causal gap.

The formalization proves

> **G* ≤ c*.**

It also proves an exact penalty representation.

For every `κ ≥ G*`,

> **C(T) = inf_Γ [ H(Γ) + κ · Γ(B) ],**

where `B` is the incompatible part of the coupling.

Relevant declarations:

```text
CausalSpectrum.causalMin_le_penalised
CausalSpectrum.penaltyMin_eq_causalMin
CausalSpectrum.gapSup_le_shannonOverhead
CausalSpectrum.penalty_shortfall
```

Thus causal compatibility can be represented exactly by penalizing incompatible mass with a sufficiently large coefficient.

---

# Infinite controlled trees

The finite construction extends to locally finite infinite controlled trees through their finite horizons.

Exactness is imposed on every finite cylinder.

---

## Atomic decomposition

Finite greedy seeds have ordered atom weights. A diagonal compactness argument produces limiting strategy atoms.

Let

```text
q = atomQ
```

denote the limiting atomic capacity.

The development constructs:

1. an atomic measure `atomMeasure` of total mass `q`;
2. a residual probability process;
3. an exact probability measure `fullMeasure`.

The decomposition is

> **μ_full = μ_atom + (1 − q) μ_res.**

For every finite history `h`,

> **μ_full([h]) = pathMass(h).**

At the level of cylinder masses,

> **cylMass(h) + resMass(∅) · resCyl(h) = pathMass(h).**

The residual component is constructive: its transition kernels are obtained directly from the residual flow.

Relevant files:

```text
CausalSeed/Atomic.lean
CausalSeed/Capacity.lean
CausalSeed/MeasureCompletion.lean
CausalSeed/AtomicCapacity.lean
```

---

## Atomic-capacity theorem

An ordinary exact source may use a separate measurable readout for every finite policy.

No causal consistency between those readouts is assumed.

Nevertheless,

> **atomicMass(μ) ≤ q**

for every ordinary exact source.

The constructed causal measure attains equality:

> **atomicMass(fullMeasure) = q.**

The principal declarations are

```text
CausalSpectrum.Completion.ordinary_atomic_upper
CausalSpectrum.Completion.causal_atomic_capacity_attained
```

Hence the ordinary atomic upper bound and the attained causal atomic value coincide.

There is also an exact dichotomy:

> **A countably supported exact seed exists if and only if q = 1.**

This is

```text
CausalSpectrum.Completion.countable_seed_iff_atomQ_one
```

and when `q = 1`, the explicit atomic measure is already exact:

```text
CausalSpectrum.Completion.discrete_seed_of_atomQ_one
```

---

## Projective entropy identity

A countable seed consists of

- nonnegative weights summing to one;
- one infinite response strategy for every atom.

A ranked seed has the same data with weights arranged in nonincreasing order.

Entropy is the extended Shannon sum in nats.

Define

```text
C_n
```

as the infimum of entropy over countable seeds exact through horizon `n`, and

```text
C_∞
```

as the infimum over countable seeds exact at every finite horizon.

Then

> **C_∞ = sup_n C_n.**

This is

```text
CausalSpectrum.Completion.projective_entropy_identity
```

The difficult direction is the infinite-horizon compactness step: bounded entropy prevents probability mass from escaping to arbitrarily high atom ranks.

If

> **sup_n C_n < ∞,**

then an exact ranked seed exists and attains `C_∞`.

This is

```text
CausalSpectrum.Completion.entropy_attained
```

Finite entropy also implies

> **q = 1.**

---

## Ranking is without loss of generality

The monotone ordering of atom weights is not an assumption on the original source.

`CausalSeed/SeedRanking.lean` proves that every arbitrary countable seed admits a ranked rearrangement preserving:

- total mass;
- every cylinder sum;
- the induced measure;
- entropy;
- finite-horizon exactness;
- infinite exactness.

The principal declaration is

```text
CausalSpectrum.Completion.CountableSeed.exists_ranked
```

and the optimization problems agree:

```text
CausalSpectrum.Completion.finiteCost_eq_countable
CausalSpectrum.Completion.infiniteCost_eq_countable
```

---

## Infinite Shannon bridge

Let

```text
L_∞ = sup_n L(T_n),
```

where `T_n` is the horizon-`n` truncation and `L(T_n)` is its finite envelope entropy in bits.

The lower bound comes from the fact that every seed exact through horizon `n` induces an ordinary coupling of the horizon-`n` transcript family.

The upper bound comes from the finite greedy seed.

After converting bits to nats,

> **(ln 2) · L_∞ ≤ C_∞ ≤ (ln 2) · (L_∞ + c*).**

This is

```text
CausalSpectrum.Completion.infiniteCost_bridge
```

and therefore

> **C_∞ < ∞  ⇔  L_∞ < ∞.**

This is

```text
CausalSpectrum.Completion.infiniteCost_lt_top_iff
```

Thus a finite-entropy exact countable seed exists exactly when the finite envelope entropies remain uniformly bounded.

---

# Further formalized results

The repository contains several independent structural results beyond the main Shannon theorem.

## Arithmetic rigidity

For a positive finite weight vector, the development studies the arithmetic obstruction created by equal subset sums.

Relevant declarations:

```text
CausalSpectrum.unrealizable_splits
CausalSpectrum.bad_mem_defect
CausalSpectrum.profile_attainment
CausalSpectrum.incompatible_mass_le
CausalSpectrum.profile_mass_attained
CausalSpectrum.exact_rigidity
CausalSpectrum.sharp_threshold
```

In particular:

> **Every exact decoder family is realizable if and only if all subset sums are distinct.**

For `ε`-accurate families, the sharp universal threshold is

> **2ε < gamma.**

The converse obstruction is attained on a controlled tree of depth at most two.

This result does not use the Shannon bound.

---

## Relabeling repair

One may allow a weight-preserving permutation of the seed separately for each policy.

The exact criterion is

```text
CausalSpectrum.relabelRepair_iff_countStable
```

and the sharp universal threshold is

```text
CausalSpectrum.sharp_relabel
```

in terms of `deltaRel`.

The repair preserves the seed weights and each individual policy law.

---

## Greedy concentration

If every policy places probability at least `a` on some `K` transcripts, then the first `M` greedy weights satisfy

> **Σ_{i < M} w_i ≥ a · (1 − (1 − 1/K)^M).**

This is

```text
CausalSpectrum.greedy_head_lower
```

The same greedy prefix is bounded above by the mass of the `M` most likely transcripts of every policy:

```text
CausalSpectrum.greedy_prefix_le_topMass
```

These estimates are the finite starting point of the infinite atomic-capacity construction.

---

# Machine verification

The project is checked with

```text
Lean    4.35.0-rc3
mathlib 7d6757bc18680044fc0ff6efc8ee20494b408556
```

The environment is pinned by

```text
lean-toolchain
lake-manifest.json
lakefile.toml
```

Build the complete development with

```bash
lake build
```

The principal declarations have also been checked with `#print axioms`.

For example,

```text
#print axioms CausalSpectrum.causal_realization
```

reports only

```text
propext
Classical.choice
Quot.sound
```

The same standard axioms occur in the principal finite and infinite-horizon results.

There is no `sorry`, `admit`, or `sorryAx` in the checked development.

See:

```text
AXIOMS.txt
```

---

# Repository map

| File | Purpose |
| --- | --- |
| `CausalSeed/Spectrum.lean` | Controlled trees, policies, strategies, minimax structure, greedy extraction |
| `CausalSeed/Entropy.lean` | Finite stochastic realization and Shannon bound |
| `CausalSeed/Gap.lean` | Envelope and ordinary coupling comparison |
| `CausalSeed/Penalty.lean` | Universal causal gap and endpoint estimates |
| `CausalSeed/Close.lean` | Removal of the compatible part |
| `CausalSeed/Transport.lean` | Residual transport through the pruned tree |
| `CausalSeed/Identity.lean` | Exact penalty identity |
| `CausalSeed/Arithmetic.lean` | Subset-sum arithmetic |
| `CausalSeed/Probe.lean` | Defect obstruction |
| `CausalSeed/Profile.lean` | Depth-two attainment and sharp threshold |
| `CausalSeed/Relabel.lean` | Relabeling repair |
| `CausalSeed/Atomic.lean` | Greedy concentration and diagonal atomic mass |
| `CausalSeed/Capacity.lean` | Infinite strategies and residual cylinder flow |
| `CausalSeed/MeasureCompletion.lean` | Atomic measure, residual product, exact mixture |
| `CausalSeed/AtomicCapacity.lean` | Ordinary upper bound and causal attainment |
| `CausalSeed/EntropyLimit.lean` | Entropy compactness and projective entropy identity |
| `CausalSeed/SeedRanking.lean` | Ranked rearrangement of arbitrary countable seeds |
| `CausalSeed/EnvelopeBridge.lean` | Infinite Shannon bridge |
| `CausalSeed/SecondOrder.lean` | Formalized profile calculations |
| `AXIOMS.txt` | Recorded axiom audit |

The root file

```text
CausalSeed.lean
```

imports the complete checked development.

---

# Principal declarations

For a compact audit, the main declarations are:

```text
CausalSpectrum.causal_realization
CausalSpectrum.causal_truncation
CausalSpectrum.one_seed_shannon

CausalSpectrum.causalMin_le_penalised
CausalSpectrum.penaltyMin_eq_causalMin
CausalSpectrum.gapSup_le_shannonOverhead
CausalSpectrum.penalty_shortfall

CausalSpectrum.Completion.causal_atomic_capacity_attained
CausalSpectrum.Completion.countable_seed_iff_atomQ_one

CausalSpectrum.Completion.projective_entropy_identity
CausalSpectrum.Completion.entropy_attained

CausalSpectrum.Completion.CountableSeed.exists_ranked
CausalSpectrum.Completion.finiteCost_eq_countable
CausalSpectrum.Completion.infiniteCost_eq_countable

CausalSpectrum.Completion.infiniteCost_bridge
CausalSpectrum.Completion.infiniteCost_lt_top_iff
```

---

# Scope

The finite theorem currently assumes:

- finite controlled history trees;
- finite nonempty action alphabets;
- finite nonempty output alphabets;
- strictly positive real transition probabilities;
- deterministic adaptive policies.

The infinite development concerns locally finite controlled trees and exact finite-cylinder laws.

Randomized policies are not primitive objects of the present finite formalization.

---

# What is not claimed

The repository does not claim:

- an exact value of `G*`;
- the square-root asymptotic suggested by the diffusion profile;
- the identity `atomQ = lim F∞`;
- that every minimizer strictly above `G*` is compatible;
- a theorem for zero-probability branches without first removing or reformulating those branches.

Only statements represented by declarations in the checked Lean import closure should be treated as machine-checked results.

---

# Build

Install `elan`, clone the repository, and run

```bash
lake build
```

Lake reads the pinned Lean toolchain and mathlib revision from the repository.

The first build downloads the dependencies. Later builds reuse them.

---

# Attribution and priority

This repository makes no claim of publication priority.

Its purpose is to provide a precise mathematical formulation and a reproducible machine-checked proof package.

If a result formalized here already appears in prior work, priority and credit belong to the original authors.
