# Exact causal seeds on controlled trees

### A machine-checked finite Shannon theorem, atomic-capacity theorem, and projective entropy identity

**Jan Mikulik — October 2026**

This repository studies a common-randomness problem for controlled stochastic processes.

A single random seed chooses a **total response strategy**.  
Every deterministic adaptive policy must then obtain the prescribed process law from that same seed.

The central finite theorem is:

\[
\boxed{
Z \preceq_{\mathrm{st}} J \preceq_{\mathrm{st}} Z+E,
\qquad
E\sim \operatorname{Exp}(\ln 2)
}
\]

and, in entropy form,

\[
\boxed{
L(T)\le H(S)\le
L(T)+\frac{1+\log_2 e}{2}.
}
\]

The seed is exact for **every deterministic adaptive policy on the tree**, and the additive constant is independent of the depth of the tree.

The formal proof is in Lean.

---

## 1. The finite theorem

Let \(T\) be a finite controlled history tree.

At every nonterminal history:

- there is a finite nonempty set of actions;
- each action has a finite nonempty output alphabet;
- the output kernel consists of strictly positive real probabilities summing to one.

A deterministic policy may choose its next action from the complete observed history.

A deterministic response strategy is stronger: it specifies an output for **every action at every history**, including branches that will not be visited by a particular policy.

A causal seed is a probability distribution over such total strategies.

The key requirement is therefore not merely to couple the transcript laws of several policies. One probability source must admit a single compatible strategy interpretation across all shared histories.

### Exact realization

`CausalSpectrum.causal_realization` proves that greedy extraction of the probability flow produces one finite seed \(S\) such that, simultaneously for every deterministic policy \(\pi\),

\[
\Pr_S[\operatorname{run}(S,\pi)=\ell]
=
\begin{cases}
p_T(\ell), & \ell\text{ is compatible with }\pi,\\
0, & \text{otherwise}.
\end{cases}
\]

The seed is chosen once. It is not selected separately for each policy.

Let

- \(J=-\log_2 W\) be the information of a seed atom of weight \(W\);
- \(Z\) be the information distribution induced by the lower envelope of the deterministic-policy transcript laws.

Then

\[
Z\preceq_{\mathrm{st}}J\preceq_{\mathrm{st}}Z+E,
\qquad
E\sim\operatorname{Exp}(\ln2).
\]

In the Lean formalization these two comparisons are

```text
seedCDF t  ≤ Fstar T t
seedTail t ≤ coupleSurv T t
```

for every real \(t\).

The second bound is exactly the survival function of \(Z+E\), with \(E\) independent of \(Z\).

---

## 2. Shannon bound

Define

\[
L(T)=\operatorname{envelopeMean}(T)
\]

in bits, and let \(H(S)\) be the Shannon entropy of the finite causal seed.

The declaration

```text
CausalSpectrum.one_seed_shannon
```

proves

\[
\boxed{
L(T)\le H(S)\le L(T)+c_*,
\qquad
c_*=\frac{1+\log_2 e}{2}.
}
\]

Numerically,

\[
c_* \approx 1.2213475204\ \text{bits}.
\]

The lower bound follows from the layer-cake representation of the envelope.  
The upper bound comes from the refined greedy cutoff estimate.

The stochastic exponential bound by itself integrates to the weaker constant \(\log_2 e\).  
The constant \(c_*\) comes from the sharper residual-mass estimate.

The constant is uniform in the horizon and in the depth of the finite tree.

---

## 3. Operational truncation

The same seed satisfies the uniform tail estimate

\[
\Pr(J>t+s)
\le
\Pr(Z>t)+2^{-s},
\qquad s\ge0.
\]

This is

```text
CausalSpectrum.causal_truncation
```

and is an operational reading of the same finite realization theorem, not a separate construction.

---

## 4. Causal versus ordinary coupling

An ordinary coupling of policy transcript laws need not be consistent at shared histories.

A causal seed must be.

Let

- \(M(T)\) denote the ordinary coupling optimum;
- \(C(T)\) denote the causal optimum;
- \(G_*\) denote the universal causal gap.

The formalization proves

\[
G_*\le c_*.
\]

It also proves the exact penalty identity

\[
\boxed{
C(T)
=
\inf_\Gamma
\left[
H(\Gamma)+\kappa\,\Gamma(B)
\right]
}
\qquad
(\kappa\ge G_*),
\]

where \(B\) is the incompatible part of an ordinary coupling.

The relevant declarations are

```text
CausalSpectrum.causalMin_le_penalised
CausalSpectrum.penaltyMin_eq_causalMin
CausalSpectrum.gapSup_le_shannonOverhead
CausalSpectrum.penalty_shortfall
```

Thus causal compatibility can be represented exactly by an entropy objective with a sufficiently large penalty on incompatible mass.

---

# Infinite controlled trees

The finite theorem has a projective infinite-horizon continuation.

The infinite tree is locally finite.  
All statements below concern exact realization of every finite cylinder.

---

## 5. Atomic capacity

Finite greedy seeds have ordered atom weights. Passing to a diagonal subsequence produces limiting strategy atoms.

Let

\[
q=\operatorname{atomQ}.
\]

The formalization constructs:

1. an atomic measure `atomMeasure` of total mass \(q\);
2. a residual probability process from the remaining cylinder flow;
3. the exact mixture

\[
\mu_{\mathrm{full}}
=
\mu_{\mathrm{atom}}
+
(1-q)\mu_{\mathrm{res}}.
\]

For every finite history \(h\),

\[
\boxed{
\mu_{\mathrm{full}}([h])
=
\operatorname{pathMass}(h).
}
\]

At the level of real cylinder masses the decomposition is

\[
\operatorname{cylMass}(h)
+
\operatorname{resMass}(\varnothing)\,
\operatorname{resCyl}(h)
=
\operatorname{pathMass}(h).
\]

The residual component is therefore not merely obtained from abstract compactness: its local transition probabilities are explicitly constructed from the residual flow.

Relevant files:

```text
CausalSeed/Atomic.lean
CausalSeed/Capacity.lean
CausalSeed/MeasureCompletion.lean
CausalSeed/AtomicCapacity.lean
```

---

## 6. Exact atomic-capacity theorem

An ordinary source is allowed a separate measurable readout for every finite policy.  
No causal compatibility between those readouts is assumed.

Nevertheless every such exact source satisfies

\[
\operatorname{atomicMass}(\mu)\le q.
\]

The constructed causal measure attains equality:

\[
\operatorname{atomicMass}(\mu_{\mathrm{full}})=q.
\]

Thus the ordinary atomic supremum and the attained causal atomic value coincide.

This is formalized by

```text
CausalSpectrum.Completion.ordinary_atomic_upper
CausalSpectrum.Completion.causal_atomic_capacity_attained
```

There is also an exact dichotomy:

\[
\boxed{
\text{a countably supported exact seed exists}
\iff
q=1.
}
\]

This is

```text
CausalSpectrum.Completion.countable_seed_iff_atomQ_one
```

and when \(q=1\), the explicitly constructed atomic measure is already exact:

```text
CausalSpectrum.Completion.discrete_seed_of_atomQ_one
```

Hence \(1-q\) is precisely the mass that cannot be carried by any countably supported exact seed.

---

## 7. Projective entropy identity

A countable seed consists of nonnegative weights summing to one and one infinite response strategy per atom.

A ranked seed has the same data with weights arranged in nonincreasing order.

Entropy is the extended sum

\[
H(S)
=
\sum_i -w_i\log w_i
\in[0,\infty],
\]

measured in nats.

Define

\[
C_n
=
\inf
\{
H(S):
S\text{ is exact through horizon }n
\}
\]

and

\[
C_\infty
=
\inf
\{
H(S):
S\text{ is exact at every finite horizon}
\}.
\]

Then

\[
\boxed{
C_\infty=\sup_n C_n.
}
\]

This is

```text
CausalSpectrum.Completion.projective_entropy_identity
```

The nontrivial direction is the infinite-horizon compactness step.  
The proof prevents entropy-bounded probability mass from escaping to arbitrarily high atom ranks.

If

\[
\sup_n C_n<\infty,
\]

then an exact ranked seed exists and attains the value \(C_\infty\):

```text
CausalSpectrum.Completion.entropy_attained
```

Consequently finite entropy implies

\[
q=1.
\]

---

## 8. Ranking is without loss of generality

The decreasing-weight condition is not an assumption on the original source.

`CausalSeed/SeedRanking.lean` proves that every arbitrary countable seed can be rearranged into ranked form while preserving

- total mass;
- every cylinder sum;
- the induced seed measure;
- Shannon entropy;
- finite-horizon exactness;
- infinite exactness.

Therefore the ranked optimization problems equal the corresponding optimization problems over all countable seeds:

```text
CausalSpectrum.Completion.finiteCost_eq_countable
CausalSpectrum.Completion.infiniteCost_eq_countable
```

---

## 9. Infinite Shannon bridge

Let

\[
L_\infty
=
\sup_n L(T_n),
\]

where \(T_n\) is the horizon-\(n\) truncation and \(L(T_n)\) is the finite envelope entropy in bits.

Every countable seed exact through horizon \(n\) induces an ordinary coupling of the horizon-\(n\) transcript family. This gives the lower bound.

The finite greedy seed gives the upper bound.

After the explicit conversion

\[
1\text{ bit}=\ln 2\text{ nats},
\]

the result is

\[
\boxed{
(\ln2)L_\infty
\le
C_\infty
\le
(\ln2)(L_\infty+c_*).
}
\]

This is

```text
CausalSpectrum.Completion.infiniteCost_bridge
```

and therefore

\[
\boxed{
C_\infty<\infty
\iff
L_\infty<\infty.
}
\]

Equivalently, a finite-entropy exact countable seed exists exactly when the finite envelope entropies remain uniformly bounded.

The formal declaration is

```text
CausalSpectrum.Completion.infiniteCost_lt_top_iff
```

---

# Further formalized results

The repository also contains several results that are logically separate from the Shannon theorem.

## Arithmetic rigidity

For a positive finite weight vector \(w\), define the subset-sum separation parameter `gamma`.

The formalization proves:

```text
CausalSpectrum.bad_mem_defect
CausalSpectrum.profile_attainment
CausalSpectrum.incompatible_mass_le
CausalSpectrum.profile_mass_attained
CausalSpectrum.exact_rigidity
CausalSpectrum.sharp_threshold
```

In particular:

\[
\text{every exact family is realizable}
\iff
\text{all subset sums are distinct},
\]

and every \(\varepsilon\)-accurate family is realizable exactly below the sharp threshold

\[
2\varepsilon<\gamma.
\]

The converse obstruction is witnessed on a controlled tree of depth at most two.

This result does not use the Shannon bound.

---

## Relabeling repair

For policy-indexed decoders one may allow a weight-preserving permutation of the seed separately for each policy.

The repository proves an exact combinatorial criterion for when this repairs the family:

```text
CausalSpectrum.relabelRepair_iff_countStable
```

and a sharp universal threshold

```text
CausalSpectrum.sharp_relabel
```

in terms of `deltaRel`, the minimum mass gap between subsets with different vectors of weight-class counts.

This parameter is distinct from `gamma`.

---

## Greedy concentration

If every policy places probability at least \(a\) on some \(K\) transcripts, then the first \(M\) greedy weights satisfy

\[
\sum_{i<M}w_i
\ge
a\left(1-\left(1-\frac1K\right)^M\right).
\]

This is

```text
CausalSpectrum.greedy_head_lower
```

The same prefix is bounded above by the mass of the \(M\) most likely transcripts of every policy:

```text
CausalSpectrum.greedy_prefix_le_topMass
```

These estimates are the finite starting point of the atomic-capacity construction.

---

# Formal verification

The project is checked with

```text
Lean    4.35.0-rc3
mathlib 7d6757bc18680044fc0ff6efc8ee20494b408556
```

The versions are pinned by

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

and the corresponding infinite-horizon declarations report only the standard Lean axioms

```text
propext
Classical.choice
Quot.sound
```

No `sorry`, `admit`, or `sorryAx` is used in the checked development.

See:

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
| `CausalSeed/Atomic.lean` | Greedy concentration and diagonal atom mass |
| `CausalSeed/Capacity.lean` | Infinite strategies and residual cylinder flow |
| `CausalSeed/MeasureCompletion.lean` | Atomic measure, residual product, exact mixture |
| `CausalSeed/AtomicCapacity.lean` | Ordinary upper bound and attained causal atomic capacity |
| `CausalSeed/EntropyLimit.lean` | Entropy compactness and \(C_\infty=\sup_n C_n\) |
| `CausalSeed/SeedRanking.lean` | Rearrangement of arbitrary countable seeds |
| `CausalSeed/EnvelopeBridge.lean` | Infinite Shannon bridge |
| `CausalSeed/SecondOrder.lean` | Formalized profile-mean calculations only |
| `AXIOMS.txt` | Recorded `#print axioms` audit |

The root import

```text
CausalSeed.lean
```

imports the complete checked development.

---

# Scope

The formalized finite theorem currently assumes:

- finite controlled history trees;
- finite nonempty action and output alphabets;
- strictly positive real transition probabilities;
- deterministic adaptive policies.

The infinite development concerns locally finite controlled trees and exact finite-cylinder laws.

Randomized policies are not a primitive object of the finite theorem.

---

# What is not claimed

To keep the formal result separate from surrounding heuristics and numerical observations, the repository does **not** claim:

- an identification of the exact numerical value of \(G_*\);
- the square-root asymptotic suggested by the diffusion profile;
- the identity `atomQ = lim F∞`;
- that every minimizer strictly above \(G_*\) must be compatible;
- a theorem for zero-probability branches without first removing or reformulating them.

Only declarations present in the Lean development should be treated as machine-checked results.

---

# Main declarations

For a quick audit, the principal statements are:

```text
CausalSpectrum.causal_realization
CausalSpectrum.one_seed_shannon
CausalSpectrum.penaltyMin_eq_causalMin
CausalSpectrum.gapSup_le_shannonOverhead

CausalSpectrum.Completion.causal_atomic_capacity_attained
CausalSpectrum.Completion.countable_seed_iff_atomQ_one
CausalSpectrum.Completion.projective_entropy_identity
CausalSpectrum.Completion.entropy_attained
CausalSpectrum.Completion.CountableSeed.exists_ranked
CausalSpectrum.Completion.infiniteCost_bridge
CausalSpectrum.Completion.infiniteCost_lt_top_iff
```

---

# Build

Install `elan`, clone the repository, and run

```bash
lake build
```

Lake reads the pinned toolchain and mathlib revision from the repository.

The first build downloads the dependencies; subsequent builds reuse them.

---

# Priority and attribution

This repository makes no claim of publication priority.

Its purpose is to provide a precise mathematical formulation and a reproducible machine-checked proof package.

If any result formalized here already appears in prior work, priority and credit belong to the original authors.
