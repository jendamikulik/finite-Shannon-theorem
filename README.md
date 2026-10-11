# One seed for every adaptive policy

**Exact causal simulation on controlled trees — formalized in Lean 4.**

**Jan Mikulík · October 2026**

Draw one random seed. Thereafter, generate every response deterministically
from the seed, the observed history, and the current action.

The same seed distribution realizes the prescribed transcript law under
**every deterministic adaptive policy**, with a decoder consistent at shared
histories.

The development connects three results:

- **Finite trees:** a universal additive entropy bound.
- **Infinite trees:** an exact criterion for finite-entropy simulation.
- **Stationary kernels:** an explicit square-root asymptotic.

## 1. Finite trees: a universal entropy bound

Let $`C(T)`$ be the minimum entropy required for exact causal simulation of
a finite controlled tree. Let $`L(T)`$ be the mean of the lower envelope
of its policy transcript information distributions.

There exists one finite greedy seed $`S_G`$ such that

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

## 2. Infinite horizons: bounded envelopes characterize finite entropy

For a locally finite infinite controlled tree, let $`C_n`$ be the infimum
of countable-seed entropy needed through horizon $`n`$, and $`C_\infty`$
the infimum for one seed exact at every finite horizon.

Expressing all entropies in bits,

```math
\boxed{C_\infty=\sup_n C_n.}
```

If this value is finite, one exact countable seed attains it.

Writing $`L_\infty=\sup_n L(T_n)`$, the same additive constant survives:

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

## 3. Stationary kernels: the exact square-root coefficient

Suppose the same finite family of output laws is available at every history,
and all actions have the same entropy $`h`$, in bits.

Let

```math
a=\max_i\sqrt{\operatorname{Var}(-\log_2 P_i(Y_i))},
\qquad
b=\min_i\sqrt{\operatorname{Var}(-\log_2 P_i(Y_i))}.
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
The result includes $`b=0`$.

When $`b>0`$, the development proves the stronger remainder estimate

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
When $`a=b`$, it establishes a vanishing square-root coefficient;
it does not establish a sharp logarithmic correction.

## Structural results

### Exact penalty for incompatibility

Let $`G_*`$ be the supremum, over finite trees, of the difference between
the causal and ordinary coupling entropy optima. The development proves

```math
\frac{2}{9}\le G_*\le c_*.
```

For every $`\kappa\ge G_*`$,

```math
C(T)=\inf_\Gamma
\bigl[H(\Gamma)+\kappa\,\Gamma(B)\bigr],
```

where $`B`$ is the incompatible part of the coupling.

For $`\kappa>G_*`$, every attained minimizer is causal. More quantitatively,
an $`\varepsilon`$-minimizer satisfies

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
$`\varepsilon`$, the sharp universal threshold is $`2\varepsilon<\gamma`$,
where $`\gamma`$ is the minimum separation between distinct subset sums.

A separate characterization treats repair by policy-dependent,
weight-preserving relabelings.

See [Profile.lean](CausalSeed/Profile.lean) and
[Relabel.lean](CausalSeed/Relabel.lean).

## Verification

The development is imported through
[CausalSeed/Main.lean](CausalSeed/Main.lean).

The repository reports a successful build without `sorry` or `admit`.
[AXIOMS.txt](AXIOMS.txt) records axiom dependencies for the declarations
listed there. Its coverage does not yet include every later declaration.

Pinned dependencies:

- Lean `4.35.0-rc3`
- Mathlib `7d6757bc18680044fc0ff6efc8ee20494b408556`

To check the project with the pinned toolchain:

```bash
lake build
```

The recorded principal declarations use the standard axioms
`propext`, `Classical.choice`, and `Quot.sound`.

The infinite-seed implementation uses extended entropy in **nats**.
The envelope comparisons explicitly convert between nats and bits.
The mathematical statements above use **bits** throughout.

## Scope and open questions

The tree models assume finite nonempty local alphabets and strictly
positive transition probabilities. Policies are deterministic and adaptive.

The following remain unresolved in this development:

- the exact value of $`G_*`$;
- compatibility of all minimizers at the endpoint $`\kappa=G_*`$;
- the proposed identity $`\mathrm{atomQ}=\lim F_\infty`$;
- a sharp logarithmic asymptotic in the equal-variance regime;
- an extension retaining zero-probability branches without reformulating
  the model.

## Attribution

The additive constant and the nonlinear diffusion profile have antecedents
in the literature. This repository makes no blanket claim of originality
or priority.

Its purpose is to state the causal simulation results precisely and provide
their formal proofs. Kernel verification establishes the formal statements;
historical attribution and comparison with prior work are separate tasks.
