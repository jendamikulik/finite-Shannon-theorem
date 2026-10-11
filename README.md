# One Seed for Every Adaptive Policy

**Exact causal simulation on controlled trees, formalized in Lean 4.**

Jan Mikulík

## Abstract

A controlled tree is a finite or locally finite game in which a policy picks an
action at each history and the environment answers with a random output drawn from
a kernel attached to that history and action. A *causal seed* is one random variable
together with a deterministic response strategy for every value. At every history and
action, all policies that reach that history see the same response. The seed is
*exact* if, under every deterministic adaptive policy, the resulting transcript has
exactly the prescribed law.

This repository proves in Lean 4 that the least entropy of an exact causal seed is
governed by one object: the lower envelope $F^*$ of the transcript-information CDFs
over all policies, and its mean $L$. Results:

- For finite trees, the optimal entropy is within the universal constant
  $c_\star=\tfrac12(1+\log_2 e)$ of $L$.
- The bound extends to infinite horizons, to atomic capacity and to Rényi entropies of
  every positive order.
- For stationary kernels this gives the sharp $\sqrt n$ asymptotic, its $W_1$
  universality, and the linear growth rate when the actions' entropies differ.
- For dyadic kernels the overhead vanishes.

Every result listed below is checked by the Lean kernel, with no `sorry` and no
axioms beyond Lean's standard three.

## Contents

1. [Setting and notation](#setting-and-notation)
2. [Main results](#main-results)
3. [Verification](#verification)
4. [Trusted definitions](#trusted-definitions)
5. [Repository layout](#repository-layout)
6. [Scope and open problems](#scope-and-open-problems)
7. [Attribution](#attribution)

## Setting and notation

- **Trees.** A finite controlled tree (`Tree`) has, at each node, finitely many
  actions and, for each action $a$, finitely many outputs $y$ with kernel
  $K_a(y)>0$ and $\sum_y K_a(y)=1$. A locally finite infinite tree (`ITree`) assigns
  such a finite positive kernel to every history. `trunc ι n []` is its depth-$n$
  truncation. A stationary kernel (`Kernel`) repeats one finite family of positive
  laws $(K_a)_a$ for $n$ rounds (`Kernel.rounds n`).
- **Policies and seeds.** Policies are deterministic and adaptive. A strategy fixes
  a response for every action at every history, including histories it never
  visits. A finite seed is a weighted list of strategies. A countable seed is a
  countable law on strategies of the infinite tree. It is exact to horizon $n$ if
  every history of length at most $n$ receives its path probability.
- **Information and envelope.** For a transcript $\ell$ of probability $p(\ell)$,
  $I(\ell)=-\log_2 p(\ell)$. For a policy $\pi$, $F_\pi(t)=\Pr_\pi[I\le t]$. The
  envelope is $F^*(t)=\min_\pi F_\pi(t)$, with mean
  $L=\int_0^\infty(1-F^*(t))\,dt$. On an infinite tree, $L_n$ is the mean at horizon
  $n$, $L_\infty=\sup_nL_n$ and $F_\infty(t)=\inf_nF^*_n(t)$.
- **Costs.** $C(T)$ is the least entropy of an exact causal coupling of a finite tree.
  $C_n$ is the least entropy of a countable seed exact to horizon $n$, and $C_\infty$
  the least entropy of a seed exact at every horizon.
- **Units.** All entropies in the statements below are in **bits**. In Lean, the
  countable-seed entropies `CountableSeed.entropy`, `finiteCost` and `infiniteCost`
  are in nats; `Kernel.costBits` and `countableInfiniteCostBits` convert to bits.
  The convention is $0\log0=0$. Infinite optima take values in $[0,\infty]$.

The constants are

```math
c_\star=\frac{1+\log_2 e}{2}\approx 1.2213475204,
\qquad
d_\alpha=\frac{\log_2\!\bigl(\tfrac12+\tfrac{2^{-\alpha}}{\alpha}\bigr)}{1-\alpha}\ \ (\alpha\ne1),
\qquad d_1=c_\star .
```

## Main results

Unless a sub-namespace is shown, Lean names are in namespace `CausalSpectrum`.

### I. Finite trees

**Theorem 1 (one seed, Shannon sandwich).** For every finite controlled tree $T$
there is a finite exact causal seed $S$, produced by a greedy bottleneck procedure,
with

```math
L(T)\;\le\;H(S)\;\le\;L(T)+c_\star .
```

Every exact coupling, causal or not, has entropy at least $L(T)$, so
$L(T)\le C(T)\le L(T)+c_\star$.

Lean:
- [`one_seed_shannon`](CausalSeed/Entropy.lean#L1767)
- [`entropy_ge_envelope`](CausalSeed/Penalty.lean#L333)
- [`ordinaryMin_ge_envelope`](CausalSeed/Penalty.lean#L660)
- [`causalMin_le_overhead`](CausalSeed/Penalty.lean#L666)

**Theorem 2 (causal realization).** The same seed is stochastically sandwiched:
$F_S(t)\le F^*(t)$ for all $t$, together with an explicit upper comparison of its
survival function. For every exact finite seed,

```math
\int_0^\infty |F^*(t)-F_S(t)|\,dt = H(S)-L(T).
```

Lean:
- [`causal_realization`](CausalSeed/Entropy.lean#L2008)
- [`seedCDF_le_Fstar`](CausalSeed/Entropy.lean#L1703)
- [`wasserstein_gap`](CausalSeed/Gap.lean#L55)

**Theorem 3 (zero-probability branches).** Let the kernels be nonnegative and
normalized, so that zero-probability branches are kept in the tree (`Zero.ZTree`).
There is a law $q$ on total strategies that is exact for every policy and satisfies
$L\le H(q)\le L+c_\star$. Every exact law has $H(q)\ge L$.

Lean:
- [`Zero.zero_closure`](CausalSeed/ZeroClosure.lean#L130)
- [`Zero.zero_lower`](CausalSeed/ZeroClosure.lean#L154)

**Theorem 4 (dyadic exactness).** Suppose every kernel entry is a power of $1/2$.
Then some exact finite seed with dyadic atoms has $F_S=F^*$, hence $H(S)=L(T)$, and
there is no overhead. For a stationary dyadic kernel,

```math
C_n = L_n\qquad\text{for every } n .
```

The key step, `Dyadic.couple`, is a comonotone refinement. Finitely many dyadic laws
of mass one have a common dyadic refinement whose information CDF is at least the
minimum of theirs.

Lean:
- [`Dyadic.dyadic_exact`](CausalSeed/DyadicTree.lean#L184)
- [`Kernel.cost_eq_envelope_of_dyadic`](CausalSeed/DyadicKernel.lean#L139)
- [`Dyadic.couple`](CausalSeed/DyadicCouple.lean#L254)
- [`Completion.finiteCost_le_atoms`](CausalSeed/DyadicKernel.lean#L117)

### II. Infinite horizons and atomic capacity

Let $\iota$ be a locally finite infinite tree with positive kernels.

**Theorem 5 (projective identity and attainment).** In nats,
$C_\infty=\sup_n C_n$. If this value is finite, it is attained by one countable seed
exact at every horizon.

Lean:
- [`Completion.projective_entropy_identity`](CausalSeed/EntropyLimit.lean#L351)
- [`Completion.entropy_attained`](CausalSeed/EntropyLimit.lean#L309)

**Theorem 6 (infinite sandwich).** For countable seeds exact at every horizon, in bits,

```math
L_\infty \;\le\; C_\infty \;\le\; L_\infty + c_\star ,
```

and, whenever $L_\infty<\infty$, an exact seed attains $C_\infty$. In particular, an
exact seed of finite entropy exists if and only if $\sup_n L_n<\infty$.

Lean:
- [`Completion.infinite_envelope_sandwich`](CausalSeed/InfiniteEnvelope.lean#L60)
- [`Completion.infinite_envelope_attained`](CausalSeed/InfiniteEnvelope.lean#L82)
- [`Completion.infiniteCost_lt_top_iff`](CausalSeed/EnvelopeBridge.lean#L395)

**Theorem 7 (atomic capacity).** Let $\mathrm{atomQ}=\sup_K\inf_{n,\pi}A_K(P_{n,\pi})$,
where $A_K$ is the total mass of the $K$ heaviest transcripts. Then:

1. Every ordinary exact source, causal or not, has atomic mass at most
   $\mathrm{atomQ}$.
2. Some exact causal probability measure on strategies has atomic mass exactly
   $\mathrm{atomQ}$.
3. An exact countably supported causal seed exists if and only if $\mathrm{atomQ}=1$.
4. The capacity is read off the envelope:

```math
\mathrm{atomQ}=\lim_{t\to\infty}F_\infty(t)=\sup_t F_\infty(t).
```

Lean:
- [`Completion.ordinary_atomic_upper`](CausalSeed/AtomicCapacity.lean#L76)
- [`Completion.causal_atomic_capacity_attained`](CausalSeed/AtomicCapacity.lean#L147)
- [`Completion.countable_seed_iff_atomQ_one`](CausalSeed/AtomicCapacity.lean#L216)
- [`atomQ_eq_lim_FInf`](CausalSeed/AtomicSpectrum.lean#L118)
- [`atomQ_eq_iSup_FInf`](CausalSeed/AtomicSpectrum.lean#L134)

### III. One seed for the whole Rényi spectrum

Let $\iota$ be as in Section II.

- An *ordinary exact source* (`RenyiInf.OrdSource`) is a countable law with, for each
  horizon, a deterministic readout of a joint transcript. Its readouts need not be
  history-consistent or consistent across horizons.
- $O_\alpha$ and $C_\alpha$ are the infima of $H_\alpha$ over ordinary and over
  causal exact sources.
- $Z$ is the envelope limit variable, a law on $[0,\infty]$ with CDF $F_\infty$ and an
  atom of mass $1-\mathrm{atomQ}$ at $+\infty$.
- $R_\alpha(Z)$ is the Rényi functional of the law of $Z$:
  $(1-\alpha)^{-1}\log_2\mathbb E\,2^{(1-\alpha)Z}$ for $\alpha\ne1$ and $\mathbb EZ$ for
  $\alpha=1$.

**Theorem 8.** Suppose an ordinary exact source exists. Then there is one countable
causal seed $S$, exact at every horizon, such that for every $\alpha>0$

```math
R_\alpha(Z)\;\le\;O_\alpha\;\le\;C_\alpha\;\le\;H_\alpha(S)\;\le\;R_\alpha(Z)+d_\alpha ,
```

and for the min-entropy

```math
H_\infty(S)=C_\infty^{\mathrm R}=O_\infty^{\mathrm R}.
```

At each order, $O_\alpha$, $C_\alpha$, $R_\alpha(Z)$ and $H_\alpha(S)$ are finite or
infinite together. Examples: $d_1=c_\star$ and $d_2=\log_2(8/5)$.

Lean:
- [`RenyiInf.one_seed_all_orders_meas`](CausalSeed/RenyiLimitMeasure.lean#L350)
  (with $R_\alpha(Z)$ computed from the measure `lawZ`)
- [`RenyiInf.one_seed_all_orders`](CausalSeed/RenyiInfinite.lean#L202)
- [`RenyiInf.RZmeas_eq`](CausalSeed/RenyiLimitMeasure.lean#L337)
  ($R_\alpha(Z)=\sup_nR_\alpha(Z_n)$)
- [`RenyiInf.simultaneous_finiteness`](CausalSeed/RenyiInfinite.lean#L232)

### IV. Stationary kernels

Let a finite family of positive laws $(K_a)_a$ be used at every round. Put
$X_a=-\log_2K_a(Y)$ for $Y\sim K_a$, and let $C_n$ and $L_n$ be the optimal cost and
the envelope mean at horizon $n$, in bits.

**Theorem 9 (sharp square-root asymptotic).** Suppose all actions have the same
entropy $h=\mathbb E X_a$. Put $a=\max_a\sigma_a$ and $b=\min_a\sigma_a$, where
$\sigma_a^2=\mathrm{Var}X_a$. Then

```math
C_n = nh+\sqrt{\tfrac{2}{\pi}}\,(a-b)\sqrt n+o(\sqrt n),
```

and the same holds for $L_n$. It also holds for the entropy of any exact finite
seeds $S_n$ with $L_n\le H(S_n)\le L_n+c_\star$, which includes the greedy seeds.

If $b>0$, there is a constant $K$ such that for all $n\ge3$

```math
\Bigl|C_n-nh-\sqrt{\tfrac{2}{\pi}}\,(a-b)\sqrt n\Bigr|\le K\,n^{1/4}\log n ,
```

and the same bound holds for the greedy seed.

Lean:
- [`Kernel.cost_tendsto`](CausalSeed/SqrtGeneral.lean#L384)
- [`Kernel.envelope_tendsto`](CausalSeed/SqrtGeneral.lean#L376)
- [`Kernel.greedy_tendsto`](CausalSeed/SqrtGeneral.lean#L391)
- [`Kernel.cost_rate`](CausalSeed/SqrtMain.lean#L122)
- [`Kernel.greedy_rate`](CausalSeed/SqrtMain.lean#L131)

**Theorem 10 ($W_1$ universality).** In the setting of Theorem 9, assume $a>0$.
Let $F_{a,b}$ be the limit profile:

```math
F_{a,b}(z)=\begin{cases}\dfrac{2b}{a+b}\,\Phi(z/b), & z\le0,\\[2mm]
1-\dfrac{2a}{a+b}\,\Phi(-z/a), & z\ge0,\end{cases}
```

which is the half-normal CDF $1-2\Phi(-z/a)$, $z>0$, when $b=0$. Let $S_n$ be
countable seeds, exact to horizon $n$, with finite entropy and with
$H(S_n)-C_n=o(\sqrt n)$. Let $J_n$ be the information of $S_n$. Then

```math
\int_{\mathbb R}\Bigl|\Pr\!\Bigl[\tfrac{J_n-nh}{\sqrt n}\le x\Bigr]-F_{a,b}(x)\Bigr|\,dx\;\longrightarrow\;0 .
```

The left side is the $W_1$ distance in its CDF form. For finite seeds the same
statement is `Kernel.universality`. The analytic core is
`Sqrt.IncFamily.L1_tendsto`:
$\int|G_n(x\sqrt n)-F_{a,b}(x)|\,dx\to0$ for the Bellman envelope $G_n$.

Lean:
- [`Kernel.universality_countable`](CausalSeed/SqrtUniversalityCountable.lean#L182)
- [`Kernel.universality`](CausalSeed/SqrtUniversality.lean#L240)
- [`Sqrt.IncFamily.L1_tendsto`](CausalSeed/SqrtUniversality.lean#L102)

**Theorem 11 (causal Shannon floor).** The entropies need not be equal. Let
$h_{\max}=\max_aH(K_a)$, $M=\max_{a,y}|{-\log_2K_a(y)}-h_{\max}|$ and
$K=\int_{\mathbb R}e^{-x^2/(2M^2)}\,dx$. For every $n\ge1$,

```math
nh_{\max}-K\sqrt n\;\le\;L_n\;\le\;C_n\;\le\;nh_{\max}+K\sqrt n+c_\star ,
\qquad\text{so}\qquad \frac{C_n}{n}\to h_{\max}.
```

Lean:
- [`Kernel.cost_floor_bounds`](CausalSeed/CausalFloor.lean#L284)
- [`Kernel.causal_floor`](CausalSeed/CausalFloor.lean#L329)
- [`Kernel.envelope_floor`](CausalSeed/CausalFloor.lean#L334)

**Theorem 12 (subadditivity).** For every stationary kernel and all $m,n$,

```math
C_{m+n}\;\le\;C_m+C_n .
```

Two seeds exact to horizons $m$ and $n$ are concatenated: the first answers at
histories of length less than $m$, the second at the later rounds, reading the
history from round $m$ on. Path masses factor over this split, so the product seed
is exact to horizon $m+n$, and its entropy is the sum of the two entropies.

Lean:
- [`Kernel.costBits_subadditive`](CausalSeed/Subadditive.lean#L191) (bits)
- [`Kernel.finiteCost_subadditive`](CausalSeed/Subadditive.lean#L175) (nats)
- [`Kernel.catSeed_exactTo`](CausalSeed/Subadditive.lean#L134)
- [`Kernel.catSeed_entropy`](CausalSeed/Subadditive.lean#L150)

**Theorem 13 (Fekete limit and exact lower bound).** By Fekete's lemma,
$C_n/n\to\inf_{n\ge1}C_n/n$. With Theorem 11 this identifies the infimum:

```math
h_{\max}=\inf_{n\ge1}\frac{C_n}{n},
\qquad\text{hence}\qquad
n\,h_{\max}\;\le\;C_n\qquad\text{for every } n\ge1 .
```

Lean:
- [`Kernel.costBits_fekete`](CausalSeed/Subadditive.lean#L210)
- [`Kernel.hmax_eq_inf`](CausalSeed/Subadditive.lean#L217)
- [`Kernel.hmax_mul_le_costBits`](CausalSeed/Subadditive.lean#L222)

### V. Structure of the causal constraint

**Theorem 14 (exact penalty).** Let $G_*=\sup_T\bigl(C(T)-O(T)\bigr)$, where $O(T)$
is the least entropy of an exact coupling that need not be causal. Then
$\tfrac29\le G_*\le c_\star$. For every $\kappa\ge G_*$,

```math
C(T)=\inf_\Gamma\bigl[H(\Gamma)+\kappa\,\Gamma(B)\bigr],
```

where $B$ is the set of incompatible joint transcripts. For $\kappa>G_*$, every
global minimizer is causal, and every $\varepsilon$-minimizer has
$\Gamma(B)\le\varepsilon/(\kappa-G_*)$.

Lean:
- [`witness_gapSup_lower`](CausalSeed/Witness.lean#L1376)
- [`gapSup_le_shannonOverhead`](CausalSeed/Penalty.lean#L710)
- [`penaltyMin_eq_causalMin`](CausalSeed/Identity.lean#L569)
- [`global_minimizer_above_gap_is_causal`](CausalSeed/StrictPenalty.lean#L74)
- [`near_minimizer_badMass_le`](CausalSeed/StrictPenalty.lean#L18)

**Theorem 15 (arithmetic rigidity).** Let $w$ be a positive weight vector with total
mass one. Every exact policy-indexed decoder family on every finite tree is causally
realizable if and only if all subset sums of $w$ are distinct. With marginal error
$\varepsilon\ge0$, every $\varepsilon$-accurate family is realizable if and only if
$2\varepsilon<\gamma$, where
$\gamma=\min_{A\ne B}\bigl|\sum_{i\in A}w_i-\sum_{i\in B}w_i\bigr|$. Repair by
weight-preserving relabelings is characterized separately.

Lean:
- [`exact_rigidity`](CausalSeed/Profile.lean#L529)
- [`sharp_threshold`](CausalSeed/Profile.lean#L548)
- [`relabelRepair_iff_countStable`](CausalSeed/Relabel.lean#L1577)

## Verification

The development is the import closure of
[`CausalSeed/Main.lean`](CausalSeed/Main.lean). Pinned toolchain:

- Lean `4.35.0-rc3` ([`lean-toolchain`](lean-toolchain))
- Mathlib `7d6757bc18680044fc0ff6efc8ee20494b408556` ([`lakefile.toml`](lakefile.toml))

Build and audit:

```bash
lake build
lake env lean scripts/AxiomAudit.lean
```

[`scripts/AxiomAudit.lean`](scripts/AxiomAudit.lean) enumerates every theorem whose
defining module is `CausalSeed.*` and computes its axioms with `collectAxioms`.
Auto-generated declarations (equation lemmas, `sizeOf_spec`, injectivity lemmas,
instances) are excluded.

[`AXIOMS.txt`](AXIOMS.txt) records the result. All **1496** theorems in the 57 project
modules depend only on `propext`, `Classical.choice` and `Quot.sound`; three depend on
no axiom. No theorem uses `sorryAx`, the build reports no `sorry` or `admit`, and the
project declares no `axiom`.

## Trusted definitions

The axiom audit certifies the proofs. It does not certify that the definitions mean
what the text says. Trust rests on the definitions below and on the statements of
the theorems above. Line numbers refer to the current revision.

| Lean name | Source | Meaning |
| --- | --- | --- |
| `Tree` | [Spectrum.lean#L20](CausalSeed/Spectrum.lean#L20) | finite controlled tree; actions `Fin nA`, outputs `Fin (nY a)`, kernel `K a y` with `Kpos : 0 < K a y`, `Ksum : ∑ y, K a y = 1` |
| `ITree`, `trunc` | [Atomic.lean#L513](CausalSeed/Atomic.lean#L513), [#L522](CausalSeed/Atomic.lean#L522) | locally finite infinite tree indexed by histories `List (ℕ × ℕ)` with positive kernels; depth-`n` truncation |
| `Kernel`, `Kernel.rounds` | [Spectrum.lean#L1296](CausalSeed/Spectrum.lean#L1296), [#L1307](CausalSeed/Spectrum.lean#L1307) | one positive kernel family repeated for `n` rounds |
| `Policy`, `Strategy`, `Leaf`, `leafMass` | [Spectrum.lean#L124](CausalSeed/Spectrum.lean#L124), [#L133](CausalSeed/Spectrum.lean#L133), [#L139](CausalSeed/Spectrum.lean#L139), [#L144](CausalSeed/Spectrum.lean#L144) | deterministic adaptive policy; total response strategy; transcript; its probability |
| `CompatiblePolicy`, `CompatibleStrategy`, `run` | [Spectrum.lean#L149](CausalSeed/Spectrum.lean#L149), [#L154](CausalSeed/Spectrum.lean#L154), [#L159](CausalSeed/Spectrum.lean#L159) | consistency of a transcript with a policy or strategy; the transcript of a strategy under a policy |
| `Atom`, `transcriptWeight`, `seedShannon`, `seedCDF` | [Spectrum.lean#L823](CausalSeed/Spectrum.lean#L823), [#L913](CausalSeed/Spectrum.lean#L913), [Entropy.lean#L648](CausalSeed/Entropy.lean#L648), [#L1393](CausalSeed/Entropy.lean#L1393) | finite seed as a weighted list of strategies; decoded transcript mass; entropy (bits); information CDF |
| `IStrategy`, `pathMass`, `policyRead` | [Capacity.lean#L557](CausalSeed/Capacity.lean#L557), [#L67](CausalSeed/Capacity.lean#L67), [AtomicCapacity.lean#L86](CausalSeed/AtomicCapacity.lean#L86) | strategy on the infinite tree; probability of a history; horizon-`n` transcript |
| `Completion.CountableSeed`, `.entropy`, `.ExactTo`, `.Exact` | [SeedRanking.lean#L20](CausalSeed/SeedRanking.lean#L20), [#L30](CausalSeed/SeedRanking.lean#L30), [#L36](CausalSeed/SeedRanking.lean#L36), [#L39](CausalSeed/SeedRanking.lean#L39) | countable law on infinite strategies; entropy (nats, in `[0,∞]`); every history of length `≤ n` (resp. every history) receives its path mass |
| `infoMass`, `policyCDF`, `Fstar` | [Entropy.lean#L53](CausalSeed/Entropy.lean#L53), [#L190](CausalSeed/Entropy.lean#L190), [#L226](CausalSeed/Entropy.lean#L226) | `-log₂ q`; information CDF of a policy; its pointwise minimum over policies |
| `envelopeMean`, `Completion.LInf`, `FInf` | [Entropy.lean#L651](CausalSeed/Entropy.lean#L651), [EnvelopeBridge.lean#L367](CausalSeed/EnvelopeBridge.lean#L367), [AtomicSpectrum.lean#L22](CausalSeed/AtomicSpectrum.lean#L22) | `L` (bits); `L_∞ = sup_n L_n`; `F_∞(t) = inf_n F*_n(t)` |
| `atomQ` | [Atomic.lean#L561](CausalSeed/Atomic.lean#L561) | `sup_K inf_{n,π}` of the mass of the `K` heaviest transcripts |
| `pmfEntropy`, `entTerm` | [Penalty.lean#L118](CausalSeed/Penalty.lean#L118), [#L52](CausalSeed/Penalty.lean#L52) | Shannon entropy (bits) of a finite law, with `entTerm 0 = 0` |
| `ordinaryMin`, `causalMin`, `gapSup` | [Penalty.lean#L626](CausalSeed/Penalty.lean#L626), [#L628](CausalSeed/Penalty.lean#L628), [#L696](CausalSeed/Penalty.lean#L696) | `O(T)`, `C(T)` over exact couplings (bits); `G_*` |
| `Completion.finiteCost`, `infiniteCost`, `Kernel.costBits` | [EntropyLimit.lean#L283](CausalSeed/EntropyLimit.lean#L283), [#L286](CausalSeed/EntropyLimit.lean#L286), [SqrtMain.lean#L99](CausalSeed/SqrtMain.lean#L99) | `C_n`, `C_∞` (nats); `C_n` in bits for a stationary kernel |
| `RenyiInf.shannonBits`, `H`, `Hinf` | [RenyiCountable.lean#L23](CausalSeed/RenyiCountable.lean#L23), [#L30](CausalSeed/RenyiCountable.lean#L30), [#L33](CausalSeed/RenyiCountable.lean#L33) | Shannon, Rényi and min-entropy of a countable law (bits, in `[0,∞]`) |
| `RenyiInf.OrdSource`, `Oα`, `Cα`, `Oinf`, `Cinf` | [RenyiSource.lean#L25](CausalSeed/RenyiSource.lean#L25), [RenyiInfinite.lean#L28](CausalSeed/RenyiInfinite.lean#L28), [#L31](CausalSeed/RenyiInfinite.lean#L31), [#L33](CausalSeed/RenyiInfinite.lean#L33), [#L35](CausalSeed/RenyiInfinite.lean#L35) | ordinary exact source; ordinary and causal Rényi optima |
| `RenyiInf.RZ`, `lawZ`, `RZmeas` | [RenyiInfinite.lean#L24](CausalSeed/RenyiInfinite.lean#L24), [RenyiLimitMeasure.lean#L117](CausalSeed/RenyiLimitMeasure.lean#L117), [#L324](CausalSeed/RenyiLimitMeasure.lean#L324) | `sup_n R_α(Z_n)`; the law of `Z` on `[0,∞] ⊂ EReal`; `R_α` of that law |
| `shannonOverhead`, `Renyi.dAlpha`, `RenyiInf.dA` | [Entropy.lean#L646](CausalSeed/Entropy.lean#L646), [RenyiFinite.lean#L180](CausalSeed/RenyiFinite.lean#L180), [RenyiCountable.lean#L36](CausalSeed/RenyiCountable.lean#L36) | `c⋆ = (1 + 1/ln 2)/2`; `d_α`; `d_α` with `d_1 = c⋆` |
| `Zero.ZTree` | [ZeroTree.lean#L255](CausalSeed/ZeroTree.lean#L255) | finite tree with nonnegative normalized kernels, all branches kept |
| `Sqrt.IncFamily.sA`, `sB`, `Flim` | [SqrtDefect.lean#L427](CausalSeed/SqrtDefect.lean#L427), [#L429](CausalSeed/SqrtDefect.lean#L429), [SqrtUniversality.lean#L26](CausalSeed/SqrtUniversality.lean#L26) | `a = max σ_a`, `b = min σ_a`; the limit profile `F_{a,b}` (half-normal if `b = 0`) |
| `Kernel.EqualEntropy`, `actEntropy`, `hmax`, `floorConst` | [SqrtBridge.lean#L19](CausalSeed/SqrtBridge.lean#L19), [CausalFloor.lean#L145](CausalSeed/CausalFloor.lean#L145), [#L150](CausalSeed/CausalFloor.lean#L150), [#L181](CausalSeed/CausalFloor.lean#L181) | common entropy `h`; `H(K_a)`; `h_max`; the Gaussian integral `K` |
| `Dyadic.wt`, `massL`, `cdfL` | [DyadicCouple.lean#L18](CausalSeed/DyadicCouple.lean#L18), [#L28](CausalSeed/DyadicCouple.lean#L28), [#L31](CausalSeed/DyadicCouple.lean#L31) | `2^{-k}`; a dyadic law as a list of (level, payload); its expectation functional and information CDF |
| `Dyadic.DyadicTree`, `Kernel.IsDyadic` | [DyadicTree.lean#L17](CausalSeed/DyadicTree.lean#L17), [DyadicKernel.lean#L132](CausalSeed/DyadicKernel.lean#L132) | every kernel entry is `(1/2)^c` with `c : ℕ` |

## Repository layout

All modules are in [`CausalSeed/`](CausalSeed); `Main.lean` imports them all.

**Finite trees**
- `Spectrum`: trees, policies, strategies, transcripts, the greedy trace, stationary kernels.
- `Entropy`: the information CDF, the envelope, the Shannon sandwich, causal realization.
- `Gap`: the CDF-gap identity and finite-tree consequences.
- `Note`: constants and finite numerical facts ($c_\star$, $\theta_\alpha$, $\log_2(8/5)$).
- `SecondOrder`: Gaussian integrals for the profile mean.
- `Probe`: policy extensions used by the lower bounds.

**Couplings, penalty and rigidity**
- `Penalty`: couplings, ordinary and causal optima, $G_*$, the penalized problem.
- `Close`, `Transport`, `Identity`: residual flows, leaf transport, the exact-penalty identity.
- `StrictPenalty`: strict compatibility above $G_*$ and its stability.
- `Witness`: the witness tree for $G_*\ge 2/9$.
- `Arithmetic`, `Profile`: subset-sum gaps and arithmetic rigidity.
- `Relabel`: repair by relabeling.

**Infinite horizons**
- `Atomic`, `Capacity`, `MeasureCompletion`, `AtomicCapacity`: infinite trees, path mass, limiting strategies, atomic capacity.
- `AtomicSpectrum`: $\mathrm{atomQ}=\lim F_\infty$.
- `EntropyLimit`, `SeedRanking`, `EnvelopeBridge`: countable seeds, ranking, the projective identity, the infinite sandwich.
- `SeedDataProcessing`, `FiniteSeedExtension`, `AlphabetSeed`, `InfiniteEnvelope`: arbitrary countable alphabets and the bit-valued infinite envelope.

**Zero-probability branches**
- `ZeroGame`, `ZeroTree`, `ZeroClosure`: an abstract finite game, trees with nonnegative kernels, the closure theorem.

**Rényi spectrum**
- `RenyiFinite`: the finite-horizon Rényi sandwich.
- `RenyiCountable`: Rényi entropy of countable laws.
- `RenyiSource`: ordinary exact sources.
- `RenyiLimit`: the diagonal limit seed.
- `RenyiInfinite`: the infinite-horizon theorem.
- `RenyiLimitLaw`, `RenyiLimitMeasure`: the law of $Z$ and its moments.

**Stationary kernels**
- `Bellman`, `BellmanCompare`: the Bellman operator and barrier propagation.
- `SqrtProfile`, `SqrtDefect`, `SqrtCompare`: the profile $F_{a,b}$, the one-step defect, the CDF comparison.
- `SqrtTails`, `SqrtMean`, `SqrtRate`, `SqrtBridge`, `SqrtMain`, `SqrtPerturb`, `SqrtGeneral`: Hoeffding tails, the mean identity, the rate, the $b=0$ perturbation, the main theorem.
- `SqrtNumerics`: integer inequalities.
- `SqrtUniversality`, `SqrtUniversalityCountable`: $W_1$ universality.
- `CausalFloor`: the causal Shannon floor.
- `Subadditive`: concatenation of seeds, $C_{m+n}\le C_m+C_n$, and the Fekete limit.
- `DyadicCouple`, `DyadicTree`, `DyadicKernel`: dyadic exactness.

**Mathematical expositions** (LaTeX/PDF at the repository root)
- `bellman_square_root`: the square-root asymptotic.
- `universal_causal_seed`: the Rényi spectrum.
- `atomic_capacity`: atomic capacity.
- `completion_proof`: infinite seeds and entropy attainment.
- `arithmetic_causality`: arithmetic rigidity.
- `causal_spectrum.pdf`, `one_seed_entropy.pdf`.

## Scope and open problems

**Scope.**
- All local alphabets are finite and nonempty.
- Policies are deterministic and adaptive.
- Theorem 3 allows zero kernel entries. All other results assume strictly positive
  kernels; zero entries of a stationary kernel could be dropped without changing any
  law, but that reduction is not formalized.
- $W_1$ is used in its CDF form $\int_{\mathbb R}|F_\mu-F_\nu|$. This Mathlib version
  has no optimal-transport definition of $W_1$, and the identification through the
  quantile coupling is not formalized.

**Open mathematical problems.**
- The exact value of $G_*\in[\tfrac29,c_\star]$, and whether all minimizers are causal
  at $\kappa=G_*$.
- The second-order term of $C_n-nh$ when $a=b$, where the $\sqrt n$ coefficient
  vanishes.
- Optimality of the constants $c_\star$ and $d_\alpha$.
- Whether $C_n-nh_{\max}=O(1)$ when exactly one action attains $h_{\max}$.
  Theorems 11 and 13 give $0\le C_n-nh_{\max}\le K\sqrt n+c_\star$. When two
  maximizing actions have different variances, Theorem 9 shows the excess grows
  like $\sqrt n$.
- Infinite-horizon versions of Theorems 5–8 for kernels with zero entries.

**Not yet formalized.**
- A classification of $C_n-nh$, for equal entropies, as $\Theta(\sqrt n)$,
  $\Theta(\log n)$ or $O(1)$ according to moment matching between the actions.
- The reduction that removes zero entries from a stationary kernel, so that
  Theorems 9–13 hold for nonnegative kernels. Lean's stationary model requires
  positive entries, and no cost is defined there for kernels with zero entries.

## Attribution

The additive constant and the nonlinear diffusion profile have antecedents in the
literature. This repository does not claim originality or priority. Its purpose is to
state the causal simulation results precisely and to provide formal proofs.
Comparison with prior work is a separate task.
