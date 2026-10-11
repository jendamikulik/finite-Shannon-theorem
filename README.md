# Exact causal seeds on controlled trees

### A machine-checked finite Shannon theorem, atomic-capacity theorem, and projective entropy identity

**Jan Mikulik — October 2026**

This repository studies exact common randomness for controlled stochastic processes.

A single random seed chooses a **total response strategy**. Every deterministic adaptive policy must then obtain the prescribed stochastic law from that same seed.

The central finite theorem is

$$
\boxed{
Z \preceq_{\mathrm{st}} J \preceq_{\mathrm{st}} Z+E,
\qquad
E\sim \operatorname{Exp}(\ln 2)
}
$$

and, in entropy form,

$$
\boxed{
L(T)\le H(S)\le
L(T)+\frac{1+\log_2 e}{2}.
}
$$

The seed is exact for **every deterministic adaptive policy on the tree**, and the additive constant is independent of the depth of the tree.

The formal development is checked in Lean.

---

## 1. The finite controlled-tree theorem

Let $T$ be a finite controlled history tree.

At every nonterminal history:

- there is a finite nonempty set of actions;
- each action has a finite nonempty output alphabet;
- the output kernel consists of strictly positive real probabilities summing to one.

A deterministic policy may choose its next action from the complete observed history.

A deterministic response strategy is stronger: it specifies an output for **every action at every history**, including branches that will not be visited by a particular policy.

A causal seed is a probability distribution over such total strategies.

The key point is therefore not merely to couple the transcript laws of several policies. One shared source of randomness must admit a single compatible strategy interpretation across all shared histories.

### Exact realization

`CausalSpectrum.causal_realization` proves that greedy extraction of the probability flow produces one finite seed $S$ such that, simultaneously for every deterministic policy $\pi$,

$$
\Pr_S\!\left[\operatorname{run}(S,\pi)=\ell\right]
=
\begin{cases}
p_T(\ell), & \ell \text{ is compatible with } \pi,\\
0, & \text{otherwise}.
\end{cases}
$$

The seed is chosen once. It is not selected separately for each policy.

Let

- $J=-\log_2 W$ be the information of a seed atom of weight $W$;
- $Z$ be the information distribution induced by the lower envelope of the deterministic-policy transcript laws.

Then

$$
\boxed{
Z\preceq_{\mathrm{st}}J\preceq_{\mathrm{st}}Z+E,
\qquad
E\sim\operatorname{Exp}(\ln2).
}
$$

In the Lean formalization the two stochastic comparisons are

```text
seedCDF t  ≤ Fstar T t
seedTail t ≤ coupleSurv T t
```

for every real $t$.

The second bound is the survival function of $Z+E$, with $E$ independent of $Z$.

---

## 2. Shannon bound

Define

$$
L(T)=\operatorname{envelopeMean}(T),
$$

measured in bits, and let $H(S)$ be the Shannon entropy of the finite causal seed.

The declaration

```text
CausalSpectrum.one_seed_shannon
```

proves

$$
\boxed{
L(T)\le H(S)\le L(T)+c_*,
\qquad
c_*=\frac{1+\log_2 e}{2}.
}
$$

Numerically,

$$
c_*\approx 1.2213475204\ \text{bits}.
$$

The lower bound is the layer-cake integral of the envelope.

The upper bound comes from the refined greedy cutoff estimate.

The stochastic exponential comparison by itself integrates to the weaker additive constant $\log_2 e$. The constant $c_*$ comes from the sharper residual-mass estimate.

The bound is uniform in the finite horizon.

---

## 3. Uniform truncation

The same seed satisfies

$$
\boxed{
\Pr(J>t+s)
\le
\Pr(Z>t)+2^{-s},
\qquad
s\ge0.
}
$$

This is the declaration

```text
CausalSpectrum.causal_truncation
```

and is an operational consequence of the same exact seed.

It is not a second construction.

---

## 4. Ordinary coupling versus causal realization

An ordinary coupling of policy transcript laws need not be consistent at shared histories.

A causal seed must be.

Let

- $M(T)$ denote the ordinary coupling optimum;
- $C(T)$ denote the causal optimum;
- $G_*$ denote the universal causal gap.

The formal development proves

$$
\boxed{
G_*\le c_*.
}
$$

It also proves an exact penalty representation.

For every coefficient $\kappa\ge G_*$,

$$
\boxed{
C(T)
=
\inf_{\Gamma}
\left[
H(\Gamma)+\kappa\,\Gamma(B)
\right],
}
$$

where $B$ is the incompatible part of the ordinary coupling.

The relevant declarations are

```text
CausalSpectrum.causalMin_le_penalised
CausalSpectrum.penaltyMin_eq_causalMin
CausalSpectrum.gapSup_le_shannonOverhead
CausalSpectrum.penalty_shortfall
```

Thus causal compatibility can be represented exactly by adding a sufficiently large penalty to incompatible mass.

---

# Infinite controlled trees

The finite construction has a projective infinite-horizon continuation.

The infinite tree is locally finite, and exactness is imposed on every finite cylinder.

---

## 5. Limiting atomic mass

Finite greedy seeds have ordered atom weights.

Passing to a diagonal subsequence produces limiting strategy atoms. Let

$$
q=\operatorname{atomQ}.
$$

The formal development constructs:

1. an atomic measure `atomMeasure` of total mass $q$;
2. a residual probability process from the remaining cylinder flow;
3. an exact probability measure

$$
\mu_{\mathrm{full}}
=
\mu_{\mathrm{atom}}
+
(1-q)\mu_{\mathrm{res}}.
$$

For every finite history $h$,

$$
\boxed{
\mu_{\mathrm{full}}([h])
=
\operatorname{pathMass}(h).
}
$$

At the level of cylinder masses,

$$
\operatorname{cylMass}(h)
+
\operatorname{resMass}(\varnothing)\,
\operatorname{resCyl}(h)
=
\operatorname{pathMass}(h).
$$

The residual component is explicit: its one-step transition probabilities are obtained from the residual flow.

Relevant files:

```text
CausalSeed/Atomic.lean
CausalSeed/Capacity.lean
CausalSeed/MeasureCompletion.lean
CausalSeed/AtomicCapacity.lean
```

---

## 6. Atomic-capacity theorem

An ordinary exact source is allowed a separate measurable readout for every finite policy.

No causal compatibility between those readouts is assumed.

Nevertheless, every such source satisfies

$$
\operatorname{atomicMass}(\mu)\le q.
$$

The constructed causal measure attains equality:

$$
\boxed{
\operatorname{atomicMass}(\mu_{\mathrm{full}})=q.
}
$$

This is formalized by

```text
CausalSpectrum.Completion.ordinary_atomic_upper
CausalSpectrum.Completion.causal_atomic_capacity_attained
```

Therefore the optimal ordinary atomic mass and the attained causal atomic mass coincide.

There is also an exact dichotomy:

$$
\boxed{
\text{a countably supported exact seed exists}
\iff
q=1.
}
$$

This is

```text
CausalSpectrum.Completion.countable_seed_iff_atomQ_one
```

and when $q=1$, the explicitly constructed atomic measure is already exact:

```text
CausalSpectrum.Completion.discrete_seed_of_atomQ_one
```

---

## 7. Projective entropy identity

A countable seed consists of

- nonnegative weights summing to one;
- one infinite response strategy for each atom.

A ranked seed has the same data with weights arranged in nonincreasing order.

Entropy is the extended sum

$$
H(S)
=
\sum_i -w_i\log w_i
\in[0,\infty],
$$

measured in nats.

Define

$$
C_n
=
\inf
\left\{
H(S):
S \text{ is exact through horizon } n
\right\}
$$

and

$$
C_\infty
=
\inf
\left\{
H(S):
S \text{ is exact at every finite horizon}
\right\}.
$$

Then

$$
\boxed{
C_\infty=\sup_n C_n.
}
$$

This is

```text
CausalSpectrum.Completion.projective_entropy_identity
```

The nontrivial direction is the infinite-horizon compactness step: bounded entropy prevents probability mass from escaping to arbitrarily high atom ranks.

If

$$
\sup_n C_n<\infty,
$$

then an exact ranked seed exists and attains $C_\infty$.

This is

```text
CausalSpectrum.Completion.entropy_attained
```

Finite entropy therefore also implies

$$
q=1.
$$

---

## 8. Ranking is without loss of generality

The decreasing-weight condition is not an assumption on the original seed.

`CausalSeed/SeedRanking.lean` proves that every arbitrary countable seed can be rearranged into ranked form while preserving:

- total mass;
- every cylinder sum;
- the induced seed measure;
- entropy;
- finite-horizon exactness;
- infinite exactness.

The principal declaration is

```text
CausalSpectrum.Completion.CountableSeed.exists_ranked
```

and consequently

```text
CausalSpectrum.Completion.finiteCost_eq_countable
CausalSpectrum.Completion.infiniteCost_eq_countable
```

show that the ranked optimization problems equal the corresponding optimization problems over arbitrary countable seeds.

---

## 9. Infinite Shannon bridge

Let

$$
L_\infty
=
\sup_n L(T_n),
$$

where $T_n$ is the horizon-$n$ truncation and $L(T_n)$ is the finite envelope entropy in bits.

Every countable seed exact through horizon $n$ induces an ordinary coupling of the joint horizon-$n$ transcript family. This gives the lower bound.

The finite greedy seed gives the upper bound.

Using

$$
1\ \text{bit}=\ln 2\ \text{nats},
$$

the formalized comparison is

$$
\boxed{
(\ln2)L_\infty
\le
C_\infty
\le
(\ln2)(L_\infty+c_*).
}
$$

This is

```text
CausalSpectrum.Completion.infiniteCost_bridge
```

and therefore

$$
\boxed{
C_\infty<\infty
\iff
L_\infty<\infty.
}
$$

This is

```text
CausalSpectrum.Completion.infiniteCost_lt_top_iff
```

Equivalently, a finite-entropy exact countable seed exists exactly when the finite envelope entropies remain uniformly bounded.

---

# Further formalized results

The repository contains several additional results that are logically separate from the finite Shannon theorem.

---

## 10. Arithmetic rigidity

For a positive finite weight vector $w$, define the subset-sum separation parameter `gamma`.

The formalization proves:

```text
CausalSpectrum.unrealizable_splits
CausalSpectrum.bad_mem_defect
CausalSpectrum.profile_attainment
CausalSpectrum.incompatible_mass_le
CausalSpectrum.profile_mass_attained
CausalSpectrum.exact_rigidity
CausalSpectrum.sharp_threshold
```

In particular,

$$
\boxed{
\text{every exact family is realizable}
\iff
\text{all subset sums are distinct}.
}
$$

For $\varepsilon$-accurate families the sharp universal threshold is

$$
\boxed{
2\varepsilon<\gamma.
}
$$

The converse obstruction is attained on a controlled tree of depth at most two.

This result does not use the Shannon bound.

---

## 11. Relabeling repair

One may weaken exact causal consistency by allowing a weight-preserving permutation of the seed separately for each policy.

The formalization proves an exact criterion:

```text
CausalSpectrum.relabelRepair_iff_countStable
```

and a sharp universal threshold:

```text
CausalSpectrum.sharp_relabel
```

in terms of `deltaRel`, the minimum mass gap between subsets with different vectors of weight-class counts.

The parameter `deltaRel` is distinct from the subset-sum separation `gamma`.

The repair preserves the seed weights and each individual policy law.

---

## 12. Greedy concentration

If every policy places probability at least $a$ on some $K$ transcripts, then the first $M$ greedy weights satisfy

$$
\boxed{
\sum_{i<M} w_i
\ge
a
\left(
1-\left(1-\frac1K\right)^M
\right).
}
$$

This is

```text
CausalSpectrum.greedy_head_lower
```

The same prefix is bounded above by the mass of the $M$ most likely transcripts of every policy:

```text
CausalSpectrum.greedy_prefix_le_topMass
```

These estimates form the finite starting point of the infinite atomic-capacity construction.

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

A complete build is

```bash
lake build
```

The principal declarations have also been audited with `#print axioms`.

For example,

```text
#print axioms CausalSpectrum.causal_realization
```

reports only the standard Lean axioms

```text
propext
Classical.choice
Quot.sound
```

The same audit has been recorded for the principal finite and infinite-horizon declarations.

There is no `sorry`, `admit`, or `sorryAx` in the checked development.

See

```text
AXIOMS.txt
```

for the recorded audit.

---

# Repository map

| File | Main role |
| --- | --- |
| `CausalSeed/Spectrum.lean` | Controlled trees, policies, strategies, minimax structure, greedy extraction |
| `CausalSeed/Entropy.lean` | Finite stochastic realization and Shannon bound |
| `CausalSeed/Gap.lean` | Envelope and ordinary coupling comparison |
| `CausalSeed/Penalty.lean` | Universal causal gap and penalty endpoints |
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
| `CausalSeed/AtomicCapacity.lean` | Ordinary upper bound and attained causal atomic capacity |
| `CausalSeed/EntropyLimit.lean` | Entropy compactness and projective entropy identity |
| `CausalSeed/SeedRanking.lean` | Rearrangement of arbitrary countable seeds |
| `CausalSeed/EnvelopeBridge.lean` | Infinite Shannon bridge |
| `CausalSeed/SecondOrder.lean` | Formalized profile-mean calculations |
| `AXIOMS.txt` | Recorded `#print axioms` audit |

The root file

```text
CausalSeed.lean
```

imports the complete checked development.

---

# Principal declarations

For a short audit, the main statements are:

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

- a finite controlled history tree;
- finite nonempty action alphabets;
- finite nonempty output alphabets;
- strictly positive real transition probabilities;
- deterministic adaptive policies.

The infinite development concerns locally finite controlled trees and exact finite-cylinder laws.

Randomized policies are not a primitive object of the formal finite theorem.

---

# What is not claimed

The repository does **not** claim:

- an exact identification of the numerical value of $G_*$;
- the square-root asymptotic suggested by the diffusion profile;
- the identity `atomQ = lim F∞`;
- that every minimizer strictly above $G_*$ must be compatible;
- a theorem for zero-probability branches without first removing or reformulating those branches.

Only statements represented by Lean declarations in the checked import closure should be treated as machine-checked results.

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

If any result formalized here already appears in prior work, priority and credit belong to the original authors.
