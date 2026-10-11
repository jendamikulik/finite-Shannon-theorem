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
| One infinite seed for all positive Rényi orders | [RenyiInfinite.lean](CausalSeed/RenyiInfinite.lean) |
| Strict-penalty compatibility and stability | [StrictPenalty.lean](CausalSeed/StrictPenalty.lean) |

[AXIOMS.txt](AXIOMS.txt) contains historical axiom-audit output for the
declarations it names. It is not a complete audit of the current import
closure. Later modules include additional `#print axioms` commands.
Earlier status paragraphs in that log describe their dated snapshots.

Pinned dependencies:

- Lean `4.35.0-rc3`
- Mathlib `7d6757bc18680044fc0ff6efc8ee20494b408556`

To check the project with the pinned toolchain:

```bash
lake build
```

The recorded principal declarations use the standard axioms
`propext`, `Classical.choice`, and `Quot.sound`.

Parts of the countable Shannon implementation use extended entropy in **nats**.
The envelope comparisons explicitly convert between nats and bits.
The Rényi layer and the mathematical statements above use **bits** throughout.

## Scope and open questions

All tree models have finite nonempty local alphabets. The finite zero-kernel
theorem allows nonnegative transitions and retains the tree shape. The
infinite and stationary developments still assume strictly positive kernels.
Policies are deterministic and adaptive.

The following remain unresolved in this development:

- the exact value of $G_*$;
- compatibility of all minimizers at the endpoint $\kappa=G_*$;
- a sharp logarithmic asymptotic in the equal-variance regime;
- optimality of the universal overhead constants;
- extension of the infinite-horizon results to kernels with zero probabilities.

The identity $\mathrm{atomQ}=\lim_{t\to\infty}F_\infty(t)$ of
`atomic_capacity.tex` is now formalized (`atomQ_eq_lim_FInf`).

Remaining formalization tasks:

- the $W_1$ universality corollary of the square-root note;
- $R_\alpha(Z)$ of the infinite envelope as a moment of a limit variable
  (in Lean it is defined as $\sup_n R_\alpha(Z_n)$).

## Attribution

The additive constant and the nonlinear diffusion profile have antecedents
in the literature. This repository makes no blanket claim of originality
or priority.

Its purpose is to state the causal simulation results precisely and provide
their formal proofs. Kernel verification establishes the formal statements;
historical attribution and comparison with prior work are separate tasks.

