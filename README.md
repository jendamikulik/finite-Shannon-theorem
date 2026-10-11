# One seed for every adaptive policy

**Exact causal simulation on controlled trees — formalized in Lean 4.**

**Jan Mikulík · October 2026**

Draw one random seed. Thereafter, generate every response deterministically
from the seed, the observed history, and the current action.

The same seed distribution realizes the prescribed transcript law under
**every deterministic adaptive policy**, with a decoder consistent at shared
histories.

The development connects four results:

- **All positive Rényi orders:** one infinite causal seed with simultaneous approximation guarantees against ordinary exact sources.
- **Finite trees:** a universal additive entropy bound, including nonnegative kernels with all branches retained.
- **Infinite trees:** atomic-capacity attainment and an exact criterion for finite-entropy simulation.
- **Stationary kernels:** an explicit square-root asymptotic.

## One seed, all Rényi orders

Consider a locally finite controlled tree with strictly positive kernels.
An **ordinary exact source** is a countable random variable with a
deterministic readout for every finite-horizon policy law. These readouts
need not agree at shared histories or across horizons. A **causal exact
source** uses one total response strategy per seed atom.

Assume an ordinary exact countable source exists. Let $O_\alpha$ and
$C_\alpha$ be the infima of Rényi entropy over ordinary and causal exact
sources, respectively. There is **one** countable causal seed $S$, exact
at every finite horizon, such that simultaneously for every $\alpha>0$,

```math
\boxed{
O_\alpha\le C_\alpha\le H_\alpha(S)\le O_\alpha+d_\alpha,
}
```

where

```math
d_\alpha=
\frac{\log_2\!\left(\frac12+\frac{2^{-\alpha}}{\alpha}\right)}
{1-\alpha}
\quad(\alpha\ne1),
\qquad
d_1=\frac{1+\log_2e}{2}.
```

The same seed attains the exact min-entropy optimum:

```math
H_\infty(S)=C_\infty^{\mathrm{R}}=O_\infty^{\mathrm{R}}.
```

Here $\mathrm{R}$ distinguishes the Rényi-order endpoint from the
time-horizon limit below. In particular,

```math
H_1(S)\le O_1+1.2213475204\ldots,
\qquad
H_2(S)\le O_2+\log_2(8/5).
```

No finite Shannon entropy assumption is required. At each positive order,
the ordinary optimum, the causal optimum, and the entropy of this same
seed are finite or infinite together. This is simultaneous approximation,
not exact minimization at every finite order.

**Main declarations**

- `CausalSpectrum.RenyiInf.one_seed_all_orders`
- `CausalSpectrum.RenyiInf.simultaneous_finiteness`

See [RenyiInfinite.lean](CausalSeed/RenyiInfinite.lean),
[RenyiSource.lean](CausalSeed/RenyiSource.lean), and
[RenyiLimit.lean](CausalSeed/RenyiLimit.lean).
Exposition: [PDF](universal_causal_seed.pdf) ·
[LaTeX](universal_causal_seed.tex).

## Finite trees: a universal entropy bound

Let $C(T)$ be the infimum of entropy required for exact causal simulation of
a finite controlled tree. Let $L(T)$ be the mean of the lower envelope
of its policy transcript information distributions.

There exists one finite greedy seed $S_G$ such that

```math
\boxed{
L(T)\le C(T)\le H(S_G)\le L(T)+c_*,
\qquad
c_*=\frac{1+\log_2 e}{2}\approx 1.2213475204\ \text{bits}.
}
```

The constant is independent of the depth, the number of policies, and the
sizes of the finite action and output alphabets.

The model allows arbitrary strictly positive real transition probabilities.
Different histories and actions may have different output alphabets.

### Why causal consistency matters

An ordinary coupling can reproduce every policy's transcript distribution
while assigning conflicting responses to a shared history.

Here each seed atom specifies one response strategy on the whole tree.
Policies that encounter the same history and choose the same action receive
the same response from that atom.

The construction therefore supplies a common causal decoder, in addition
to the required marginal laws.

**Main declarations**

- `CausalSpectrum.causal_realization`
- `CausalSpectrum.one_seed_shannon`
- `CausalSpectrum.causal_truncation`

See [Entropy.lean](CausalSeed/Entropy.lean).

### Zero-probability branches remain in the tree

The finite theorem extends to nonnegative normalized kernels. The
`CausalSpectrum.Zero.ZTree` model retains the full tree shape, all policies,
and all total response strategies, including their values at
zero-probability histories.

The closure theorem constructs a finite law on these strategies satisfying
the same exact transcript identities and the same bound $L\le H\le L+c_*$.
It does not require pruning zero-probability branches. The result establishes
existence; it does not identify the limiting seed with a particular greedy run.

Exactness concerns transcript laws. It does not prescribe conditional
probabilities given an event of probability zero.

**Main declarations**

- `CausalSpectrum.Zero.zero_closure`
- `CausalSpectrum.Zero.zero_lower`

See [ZeroClosure.lean](CausalSeed/ZeroClosure.lean),
[ZeroTree.lean](CausalSeed/ZeroTree.lean), and
[ZeroGame.lean](CausalSeed/ZeroGame.lean).

## Infinite horizons: bounded envelopes characterize finite entropy

For a locally finite infinite controlled tree with strictly positive kernels, let $C_n$ be the infimum
of countable-seed entropy needed through horizon $n$, and $C_\infty$
the infimum for one seed exact at every finite horizon.

Expressing all entropies in bits,

```math
\boxed{C_\infty=\sup_n C_n.}
```

If this value is finite, one exact countable seed attains it.

Writing $L_\infty=\sup_n L(T_n)$, the same additive constant survives:

```math
\boxed{
L_\infty\le C_\infty\le L_\infty+c_*.
}
```

Consequently,

```math
\boxed{
\text{An exact finite-entropy seed exists}
\iff
\sup_n L(T_n)<\infty.
}
```

The passage to ranked weights preserves entropy and every cylinder law;
the result applies to seeds on arbitrary countable alphabets.

The development also identifies the maximal atomic mass of an exact source:
ordinary and causal atomic capacities coincide at `atomQ`, and the causal
capacity is attained. An exact countably supported seed exists precisely
when `atomQ = 1`. Countable support alone does not imply finite entropy.

**Main declarations**

- `Completion.projective_entropy_identity`
- `Completion.infiniteCost_lt_top_iff`
- `Completion.infinite_envelope_sandwich`
- `Completion.infinite_envelope_attained`
- `Completion.causal_atomic_capacity_attained`
- `Completion.countable_seed_iff_atomQ_one`

These names are under `CausalSpectrum`.

See [EntropyLimit.lean](CausalSeed/EntropyLimit.lean),
[EnvelopeBridge.lean](CausalSeed/EnvelopeBridge.lean), and
[AtomicCapacity.lean](CausalSeed/AtomicCapacity.lean).

### Atomic capacity and the information spectrum

Let $P_{n,\pi}$ be the transcript law under policy $\pi$ through horizon $n$.
Define

```math
F_\infty(t)
=
\inf_{n,\pi}
\Pr_{X\sim P_{n,\pi}}
\bigl[-\log_2 P_{n,\pi}(X)\le t\bigr].
```

The mathematical argument in [atomic_capacity.tex](atomic_capacity.tex)
establishes

```math
\boxed{
\mathrm{atomQ}=\lim_{t\to\infty}F_\infty(t).
}
```

Thus an exact countably supported causal seed exists if and only if the
information contents of all finite-policy transcript laws are uniformly
tight:

```math
\forall\varepsilon>0\ \exists t<\infty\ \forall n,\pi:
\quad
\Pr_{X\sim P_{n,\pi}}
\bigl[-\log_2 P_{n,\pi}(X)>t\bigr]\le\varepsilon.
```

The spectral identity is formalized as `CausalSpectrum.atomQ_eq_lim_FInf`
(with `atomQ_eq_iSup_FInf`) in [AtomicSpectrum.lean](CausalSeed/AtomicSpectrum.lean),
where $F_\infty(t)=\inf_n F_n(t)$ is `FInf`. The tightness reformulation above
is its immediate consequence together with `countable_seed_iff_atomQ_one`;
it is not stated as a separate Lean theorem.

## Stationary kernels: the exact square-root coefficient

Suppose the same finite family of strictly positive output laws is available at every history,
and all actions have the same entropy $h$, in bits.

For $Y_i\sim P_i$, let

```math
a=\max_i\sqrt{\mathrm{Var}(-\log_2 P_i(Y_i))},
\qquad
b=\min_i\sqrt{\mathrm{Var}(-\log_2 P_i(Y_i))}.
```

Then the optimal exact causal seed entropy satisfies

```math
\boxed{
C_n
=
nh+\sqrt{\frac{2}{\pi}}\,(a-b)\sqrt{n}+o(\sqrt{n}).
}
```

The envelope mean and the greedy seed entropy have the same expansion.
The result includes $b=0$.

When $b>0$, the development proves the stronger remainder estimate

```math
C_n
=
nh+\sqrt{\frac{2}{\pi}}\,(a-b)\sqrt{n}
+O(n^{1/4}\log n).
```

The implicit constant depends on the fixed kernel.

The proof passes from the discrete adaptive Bellman envelope to its
diffusion profile, controls the tails, and transfers the resulting mean
asymptotic through the finite entropy sandwich.

**Main declarations**

- `CausalSpectrum.Kernel.envelope_tendsto`
- `CausalSpectrum.Kernel.cost_tendsto`
- `CausalSpectrum.Kernel.greedy_tendsto`
- `CausalSpectrum.Kernel.cost_rate`

See [SqrtGeneral.lean](CausalSeed/SqrtGeneral.lean),
[SqrtMain.lean](CausalSeed/SqrtMain.lean), and the
[mathematical exposition](bellman_square_root.pdf).

This theorem requires common entropy and a stationary kernel.
When $a=b$, it establishes a vanishing square-root coefficient;
it does not establish a sharp logarithmic correction.

### Unequal entropies: the causal Shannon floor

For every finite stationary positive kernel, with $h_{\max}=\max_a H(K_a)$ (bits) and
$K=\int_{\mathbb R}e^{-x^2/(2M^2)}\,dx$ ($M=\max|{-\log_2K_a(y)}-h_{\max}|$), for $n\ge1$
$$
nh_{\max}-K\sqrt n\;\le\;L_n\;\le\;C_n\;\le\;nh_{\max}+K\sqrt n+c_\star,
\qquad\text{hence}\qquad \frac{C_n}{n}\to h_{\max}.
$$
Entropies need not be equal. Recentred at $h_{\max}$, every increment has nonpositive
mean, so the conditional Hoeffding bound still controls the upper envelope tail; a
constant policy at a maximizing action controls the lower tail.

**Main declarations** ([CausalFloor.lean](CausalSeed/CausalFloor.lean)):
`Kernel.cost_floor_bounds`, `Kernel.causal_floor`, `Kernel.envelope_floor`,
`Kernel.envelope_le_floor`, `Kernel.floor_le_envelope`.

Provenance: this statement is the "causal Shannon floor"
$C^{\mathrm{causal}}_\infty=\max\{H(P),H(Q)\}$ of DREAM6 `WHO_PAYS_THE_BILL_v5.tex`
(Theorem 17.1). The Lean proof takes a different route. It covers any number of actions
and gives the full limit of $C_n/n$ with an $O(\sqrt n)$ residual; the DREAM6 proof uses
an anti-diagonal block source along $n=mL$ and gives $O(n^{2/3})$ (its Corollary 17.2).
The Lean result needs strictly positive kernels (`Kernel.Kpos`). Zero entries can be
dropped from a stationary kernel without changing any law, but the reduction is not
formalized.

## Structural results

### Exact penalty for incompatibility

Let $G_*$ be the supremum, over finite trees, of the difference between
the causal and ordinary coupling entropy optima. The development proves

```math
\frac{2}{9}\le G_*\le c_*.
```

For every $\kappa\ge G_*$,

```math
C(T)=\inf_\Gamma
\bigl[H(\Gamma)+\kappa\,\Gamma(B)\bigr],
```

where $B$ is the incompatible part of the coupling.

For $\kappa>G_*$, every attained minimizer is causal. More quantitatively,
an $\varepsilon$-minimizer satisfies

```math
\Gamma(B)\le\frac{\varepsilon}{\kappa-G_*}.
```

See [Identity.lean](CausalSeed/Identity.lean),
[StrictPenalty.lean](CausalSeed/StrictPenalty.lean), and
[Witness.lean](CausalSeed/Witness.lean).

### Arithmetic rigidity

For a fixed positive finite weight vector, every exact policy-indexed
decoder family on every finite controlled tree is causally realizable
if and only if all subset sums are distinct.

Subset-sum collisions bound the possible incompatible mass, and suitable
trees of depth at most two attain the obstruction. With marginal error
$\varepsilon$, the sharp universal threshold is $2\varepsilon<\gamma$,
where

```math
\gamma=\min_{A\ne B}
\left|\sum_{i\in A}w_i-\sum_{i\in B}w_i\right|.
```

In particular, $\gamma=0$ when two different subsets have the same weight.

A separate characterization treats repair by policy-dependent,
weight-preserving relabelings.

See [Profile.lean](CausalSeed/Profile.lean) and
[Relabel.lean](CausalSeed/Relabel.lean).

## Verification

The development is imported through
[CausalSeed/Main.lean](CausalSeed/Main.lean).

The import closure includes the finite, infinite-horizon, square-root,
zero-kernel, and Rényi developments.

| Result | Principal Lean source |
| --- | --- |
| Finite causal realization and Shannon bound | [Entropy.lean](CausalSeed/Entropy.lean) |
| Finite nonnegative kernels, all branches retained | [ZeroClosure.lean](CausalSeed/ZeroClosure.lean) |
| Projective entropy identity and attainment | [EntropyLimit.lean](CausalSeed/EntropyLimit.lean) |
| Ordinary and causal atomic capacities | [AtomicCapacity.lean](CausalSeed/AtomicCapacity.lean) |
| General square-root limit | [SqrtGeneral.lean](CausalSeed/SqrtGeneral.lean) |
| $W_1$ universality of asymptotically optimal seeds | [SqrtUniversality.lean](CausalSeed/SqrtUniversality.lean), [SqrtUniversalityCountable.lean](CausalSeed/SqrtUniversalityCountable.lean) |
| One infinite seed for all positive Rényi orders | [RenyiInfinite.lean](CausalSeed/RenyiInfinite.lean) |
| $R_\alpha(Z)$ of the limit envelope law | [RenyiLimitLaw.lean](CausalSeed/RenyiLimitLaw.lean), [RenyiLimitMeasure.lean](CausalSeed/RenyiLimitMeasure.lean) |
| Strict-penalty compatibility and stability | [StrictPenalty.lean](CausalSeed/StrictPenalty.lean) |

[AXIOMS.txt](AXIOMS.txt) is a full axiom audit of all 1429 theorems declared in the
52 project modules (`CausalSeed.*`) reachable from `Main.lean`. Auto-generated
declarations (equation lemmas, `sizeOf_spec`, injectivity lemmas, instances) are excluded.
All 1429 depend only on `propext`, `Classical.choice` and `Quot.sound` (3 on none). No
theorem uses `sorryAx`, the build reports no `sorry` or `admit`, and no `axiom` is
declared in the project. The notes from earlier dated audit logs are kept at the end
of the file.

Pinned dependencies:

- Lean `4.35.0-rc3`
- Mathlib `7d6757bc18680044fc0ff6efc8ee20494b408556`

To check the project with the pinned toolchain and reproduce the audit:

```bash
lake build
lake env lean scripts/AxiomAudit.lean
```

The script ([scripts/AxiomAudit.lean](scripts/AxiomAudit.lean)) walks the environment,
keeps the theorems whose module is `CausalSeed.*`, runs `collectAxioms` on each, and
prints one line per theorem plus a `TOTAL` line with any non-standard axioms.

Parts of the countable Shannon implementation use extended entropy in **nats**.
The envelope comparisons explicitly convert between nats and bits.
The Rényi layer and the mathematical statements above use **bits** throughout.

## What a reviewer must check: the trusted definitions

The axiom audit certifies that every proof is complete. It does not certify that
the Lean definitions mean what the prose says. Trust therefore rests on the small set
of definitions below and on the statements of the main theorems. All names are in
namespace `CausalSpectrum` unless a sub-namespace is shown. Line numbers refer to the
current revision.

| Lean name | Source | Plain meaning |
| --- | --- | --- |
| `Tree` | [Spectrum.lean#L20](CausalSeed/Spectrum.lean#L20) | finite controlled tree; each node has actions `Fin nA`, responses `Fin (nY a)`, a kernel `K a y` with `Kpos : 0 < K a y` and `Ksum : ∑ y, K a y = 1` |
| `ITree`, `trunc` | [Atomic.lean#L513](CausalSeed/Atomic.lean#L513), [#L522](CausalSeed/Atomic.lean#L522) | infinite tree indexed by histories `List (ℕ × ℕ)`, kernels `kern` with `kpos`, `ksum`; `trunc ι n h` is its depth-`n` tree |
| `Kernel`, `Kernel.rounds` | [Spectrum.lean#L1296](CausalSeed/Spectrum.lean#L1296), [#L1307](CausalSeed/Spectrum.lean#L1307) | one stationary positive kernel repeated for `n` rounds |
| `Policy`, `Strategy`, `Leaf`, `run`, `CompatiblePolicy` | [Spectrum.lean#L124](CausalSeed/Spectrum.lean#L124)–[#L159](CausalSeed/Spectrum.lean#L159) | deterministic adaptive policy (action chosen from the full history); a strategy fixes a response at every node; `run s π` is the transcript; `leafMass` ([#L144](CausalSeed/Spectrum.lean#L144)) is its probability |
| `IStrategy`, `policyRead` | [Capacity.lean#L557](CausalSeed/Capacity.lean#L557), [AtomicCapacity.lean#L88](CausalSeed/AtomicCapacity.lean#L88) | infinite response strategy; its horizon-`n` transcript under a policy |
| `Atom`, `transcriptWeight`, `seedShannon` | [Spectrum.lean#L823](CausalSeed/Spectrum.lean#L823), [#L913](CausalSeed/Spectrum.lean#L913), [Entropy.lean#L648](CausalSeed/Entropy.lean#L648) | finite seed = weighted list of strategies; mass decoded onto each transcript; its Shannon entropy (bits) |
| `Completion.CountableSeed`, `.ExactTo`, `.Exact`, `.entropy` | [SeedRanking.lean#L20](CausalSeed/SeedRanking.lean#L20)–[#L39](CausalSeed/SeedRanking.lean#L39) | countable law on infinite strategies; exact to `n` = every history of length `≤ n` gets its path mass (history-consistent decoder); entropy in nats |
| `infoMass`, `policyCDF`, `Fstar` | [Entropy.lean#L53](CausalSeed/Entropy.lean#L53), [#L190](CausalSeed/Entropy.lean#L190), [#L226](CausalSeed/Entropy.lean#L226) | `-log₂ q`; CDF of transcript information under a policy; lower envelope over policies |
| `envelopeMean` (`L_n`), `Completion.LInf` | [Entropy.lean#L651](CausalSeed/Entropy.lean#L651), [EnvelopeBridge.lean#L367](CausalSeed/EnvelopeBridge.lean#L367) | mean of the envelope law (bits); `L_∞ = sup_n L_n` in `[0, ∞]` |
| `FInf` | [AtomicSpectrum.lean#L22](CausalSeed/AtomicSpectrum.lean#L22) | `F_∞(t) = inf_n F_n(t)` |
| `atomQ` | [Atomic.lean#L561](CausalSeed/Atomic.lean#L561) | causal atomic capacity (sup of the uniform top-`K` masses) |
| `pmfEntropy`, `entTerm` | [Penalty.lean#L118](CausalSeed/Penalty.lean#L118), [#L52](CausalSeed/Penalty.lean#L52) | Shannon entropy (bits) of a finite law |
| `RenyiInf.shannonBits`, `renyiNe`, `H`, `Hinf` | [RenyiCountable.lean#L23](CausalSeed/RenyiCountable.lean#L23)–[#L33](CausalSeed/RenyiCountable.lean#L33) | Shannon, Rényi (order `α`) and min-entropy of a countable law, bits, values in `[0, ∞]` |
| `Completion.finiteCost`, `infiniteCost`, `Kernel.costBits` | [EntropyLimit.lean#L284](CausalSeed/EntropyLimit.lean#L284), [#L287](CausalSeed/EntropyLimit.lean#L287), [SqrtMain.lean#L99](CausalSeed/SqrtMain.lean#L99) | optimal entropy of seeds exact to `n` / at all horizons (nats); `C_n` in bits |
| `RenyiInf.OrdSource`, `Oα`, `Cα`, `RZ`, `lawZ`, `RZmeas` | [RenyiSource.lean#L25](CausalSeed/RenyiSource.lean#L25), [RenyiInfinite.lean#L24](CausalSeed/RenyiInfinite.lean#L24)–[#L31](CausalSeed/RenyiInfinite.lean#L31), [RenyiLimitMeasure.lean#L117](CausalSeed/RenyiLimitMeasure.lean#L117), [#L324](CausalSeed/RenyiLimitMeasure.lean#L324) | ordinary (possibly history-inconsistent) exact source; ordinary/causal Rényi optima; `sup_n R_α(Z_n)`; the law of `Z` on `[0,∞] ⊆ EReal`; `R_α` from that law |
| `shannonOverhead`, `Renyi.dAlpha`, `RenyiInf.dA` | [Entropy.lean#L646](CausalSeed/Entropy.lean#L646), [RenyiFinite.lean#L180](CausalSeed/RenyiFinite.lean#L180), [RenyiCountable.lean#L36](CausalSeed/RenyiCountable.lean#L36) | `c⋆ = (1 + 1/ln 2)/2`; the Rényi constant `d_α`; `dA 1 = c⋆` |
| `Kernel.actEntropy`, `Kernel.hmax`, `Kernel.floorConst` | [CausalFloor.lean#L146](CausalSeed/CausalFloor.lean#L146), [#L151](CausalSeed/CausalFloor.lean#L151), [#L182](CausalSeed/CausalFloor.lean#L182) | `H(K_a)` in bits; `h_max = max_a H(K_a)`; the constant `∫ exp(-x²/(2M²)) dx` |
| `Zero.ZTree` (`.P`, `.L`) | [ZeroTree.lean#L255](CausalSeed/ZeroTree.lean#L255) | finite tree whose kernels may vanish (`Valid`: `K ≥ 0`, sums 1); all branches kept |

Main statements to read:
[`one_seed_shannon`](CausalSeed/Entropy.lean#L1767),
[`causal_realization`](CausalSeed/Entropy.lean#L2008),
[`Kernel.cost_tendsto`](CausalSeed/SqrtGeneral.lean#L384),
[`Kernel.cost_rate`](CausalSeed/SqrtMain.lean#L122),
[`Zero.zero_closure`](CausalSeed/ZeroClosure.lean#L130),
[`RenyiInf.one_seed_all_orders_meas`](CausalSeed/RenyiLimitMeasure.lean#L350),
[`atomQ_eq_lim_FInf`](CausalSeed/AtomicSpectrum.lean#L118),
[`Kernel.universality_countable`](CausalSeed/SqrtUniversalityCountable.lean#L182),
[`Kernel.causal_floor`](CausalSeed/CausalFloor.lean#L330),
[`Kernel.cost_floor_bounds`](CausalSeed/CausalFloor.lean#L285).

Conventions: entropies are in bits except `CountableSeed.entropy`, `finiteCost` and
`infiniteCost` (nats; `costBits` divides by `ln 2`). `0 log 0 = 0` (`entTerm 0 = 0`,
`Real.negMulLog 0 = 0`). Values in `ℝ≥0∞` may be `∞` (infinite optima, `L_∞`, `R_α`,
`H`, `Hinf`); `lawZ` puts mass `1 - atomQ` at `+∞`.

## Scope and open questions

All tree models have finite nonempty local alphabets. The finite zero-kernel
theorem allows nonnegative transitions and retains the tree shape. The
infinite and stationary developments still assume strictly positive kernels.
Policies are deterministic and adaptive.

The following remain unresolved in this development. They are open mathematical
questions (no proof is known to us), not formalization tasks:

- the exact value of $G_*$ (only bounds are proved);
- compatibility of all minimizers at the endpoint $\kappa=G_*$;
- a sharp logarithmic asymptotic in the equal-variance regime (the square-root
  theorem gives the $\sqrt n$ term $\sqrt{2/\pi}(a-b)$, which vanishes when $a=b$; the
  next order is not determined by the notes). DREAM6 (`equal_entropy_sublog.tex`,
  `moment_thresholds.tex`) proposes an exact dyadic recursion and a
  $\Theta(\sqrt n)/\Theta(\log n)$/bounded classification. These are not formalized
  here, so this item stays open in this repository;
- optimality of the universal overhead constants;
- extension of the infinite-horizon results to kernels with zero probabilities (the
  finite case is `Zero.zero_closure`; the infinite proofs use $\kappa>0$ in compactness
  and positivity of path masses, and no replacement argument is written down).

Closed formalization items:

- $\mathrm{atomQ}=\lim_{t\to\infty}F_\infty(t)$: `atomQ_eq_lim_FInf`.
- $W_1$ universality of the square-root note, in CDF form
  $W_1(\mu,\nu)=\int_{\mathbb R}|F_\mu-F_\nu|$: for finite seeds `Kernel.universality`
  ([SqrtUniversality.lean](CausalSeed/SqrtUniversality.lean)), for countable seeds with
  finite entropy `Kernel.universality_countable`
  ([SqrtUniversalityCountable.lean](CausalSeed/SqrtUniversalityCountable.lean)); the
  analytic core is `Sqrt.IncFamily.L1_tendsto`.
- The law of the limit variable $Z$ as a probability measure on $[0,\infty]\subset$
  `EReal` (`RenyiInf.lawZ`: the Stieltjes measure of $F_\infty$ plus an atom of mass
  $1-\mathrm{atomQ}$ at $\infty$), with moments as Lebesgue integrals equal to the tail
  formulas (`moment_lt`, `moment_one`, `moment_gt`) and
  $R_\alpha(Z)=\sup_n R_\alpha(Z_n)$ for all $\alpha>0$ (`RZmeas_eq`, `RZlaw_eq`),
  restated as `one_seed_all_orders_meas`
  ([RenyiLimitMeasure.lean](CausalSeed/RenyiLimitMeasure.lean)).

- The causal Shannon floor $C_n/n\to\max_aH(K_a)$ for unequal entropies:
  `Kernel.causal_floor` (from DREAM6, see above).

Remaining formalization tasks:

- DREAM6 items not yet ported: exact dyadic optimality $C_n=H(R_n)$
  (`equal_entropy_sublog.tex` thm:optimal; the inequality $F_S\le F_n$ is already
  `seedCDF ≤ Fstar` here, so only attainment is missing), the moment classification
  (`moment_thresholds.tex`), bounded excess for unequal entropies
  (`bounded_causal_tax.tex`; only the $O(\sqrt n)$ residual is formalized), subadditivity
  of $C_n$, the $W_1$ contract converse, and zero-repair.

- identifying the CDF form of $W_1$ with the coupling (optimal-transport) definition.
  Mathlib in this version has no Wasserstein or optimal-transport definition; the
  equivalence needs the quantile coupling, which is not formalized here.

## Attribution

The additive constant and the nonlinear diffusion profile have antecedents
in the literature. This repository makes no blanket claim of originality
or priority.

Its purpose is to state the causal simulation results precisely and provide
their formal proofs. Kernel verification establishes the formal statements;
historical attribution and comparison with prior work are separate tasks.

