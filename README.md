# An exact causal seed on a finite controlled tree

Jan Mikulik, 5 October 2026.

**One seed realises every adaptive policy, and its information stays within one exponential of the envelope. The gap does not grow with the horizon.**

That is the theorem of this repository, `CausalSpectrum.causal_realization`, checked in Lean. It is the result to read and to cite. The diffusion profile of the square-root asymptotic is not this result, and the numerical value of the gap is not a new Shannon limit.

## The theorem

For every finite controlled history tree, greedy extraction of the probability flow produces one finite seed which is an exact decoder for every deterministic policy. Let `Z` be the information of the lower envelope of the deterministic-policy transcript laws, and let `J` be the information of that seed. Then

```text
Z  ≼_st  J  ≼_st  Z + E,        E ~ Exp(ln 2).
```

`E` has rate `ln 2`, hence mean `log₂ e`. In the formalization the two comparisons are, for every real `t`,

```text
seedCDF t ≤ F⋆(t)
seedTail t ≤ coupleSurv t
```

`coupleSurv t` is `∑ μᵢ min(1, 2^(zᵢ − t))`, which is `P(Z + E > t)` for `E` independent of `Z`. For each finite controlled tree, one seed works for every deterministic adaptive policy on that tree. The seed may depend on the tree and its horizon; the overhead bound is independent of the horizon. Nothing in the gap depends on the depth of the tree.

Integrating the tails gives `L ≤ H ≤ L + log₂ e`. The declaration `CausalSpectrum.one_seed_shannon` is that integral with the residual-mass refinement

```text
L ≤ H ≤ L + (1 + log₂ e) / 2.
```

The refinement sharpens the integral. It does not replace the stochastic bound by a smaller exponential.

## Corollary

The same seed gives a uniform truncation. `CausalSpectrum.causal_truncation` is this reading of `causal_realization`, not a second discovery. For every real `t` and every `s ≥ 0`,

```text
Pr(J > t + s) ≤ Pr(Z > t) + 2^{−s}.
```

In the formalization that is `seedTail (t + s) ≤ (1 − F⋆(t)) + 2^{−s}`. Atoms of weight at least `2^{−u}` number at most `2^u`. Therefore, if `0 < ε ≤ 2` and `1 − F⋆(t) ≤ ε / 2`, the choice `s = log₂(2 / ε)` leaves at most

```text
⌊2^{t+1} / ε⌋
```

atoms, and the discarded mass is at most `ε`. Renormalising those atoms moves the seed by at most `ε` in total variation. Every function of the seed moves by at most that much: every deterministic-policy transcript, and every stopping time inside this same finite tree. One truncation serves all of them at once.

It does not control the conditional kernel at one history whose probability is much smaller than `ε`. The guarantee is on the law of what the path actually shows.

## Separate compressions, one prefix

We assume this quantitative bound is already known. The note records it because it follows from the checked minimax and extraction lemmas. It is not a Lean theorem of this repository, and it is not claimed as a discovery.

Let `0 ≤ ε < 1`. For each deterministic policy `π` let `k_ε(P_π)` be the smallest number of transcripts that carry probability at least `1 − ε`, and let `K` be the maximum of `k_ε(P_π)` over policies. Thus `K ≥ 1`. Each policy, compressed on its own, keeps mass `1 − ε` in at most `K` transcripts. Those sets need not agree.

Keep the first `M ≥ 1` atoms of the same greedy seed and renormalise them. If the extraction has already ended, keep the whole seed and the error is zero. Otherwise the renormalised seed has at most `M` values and, simultaneously for every policy, total-variation error at most

```text
ε + (1 − ε) (1 − 1/K)^M.
```

The reason is the residual flow. After `m` extractions its root mass is `R_m`, with `R_0 = 1`. The minimax identity supplies a policy whose largest residual leaf equals the next greedy weight `w_{m+1}`. On that policy, some set of at most `K` transcripts carries original mass at least `1 − ε`, so the residual outside it is at most `ε`. Hence `R_m − ε ≤ K w_{m+1}`. Extracting the atom gives

```text
R_{m+1} − ε ≤ (1 − 1/K) (R_m − ε).
```

The discarded mass after `M` atoms is `R_M`, which is the total-variation distance caused by renormalising the prefix. A deterministic decoder does not increase it. One prefix serves every policy.

For `0 < δ < 1 − ε` the choice

```text
M = ⌈K ln((1 − ε) / δ)⌉
```

makes the error at most `ε + δ`. The comparison `−ln(1 − 1/K) ≥ 1/K` makes this `M` sufficient, not necessarily smallest. An extra error `0.01` therefore costs at most `⌈4.606 K⌉` seed values. That count is a number of seed states, not a number of uniform random bits.

`K` is a cardinality of a `(1 − ε)`-support, not a Shannon entropy. Depth and the number of policies do not appear as a further factor. They can increase `K` itself. The price of using one compatible seed, rather than a separate compression for each policy, is this logarithmic multiple of `K`.

## Repair of an inconsistent coupling

We assume this repair is already known. It is not claimed as a discovery. The argument below uses the checked bound `H ≤ L + c_*` with `c_* = (1 + log₂ e) / 2`. The infimum identity for every coefficient at least `c_*` is `CausalSpectrum.penaltyMin_eq_causalMin`, because `gapSup ≤ c_*`. The total-variation reconstruction written in this section, and the claim that every minimiser strictly above the coefficient is compatible, are not separate Lean theorems.

Let `Γ` be any coupling of the exact transcript laws of all deterministic policies, and let `B` be the set of transcript tuples that no single causal strategy produces. Write `η = Γ(B)`. Let `C` be the least entropy of an exact causal seed.

There is a compatible coupling `Γ̂` with the same marginals such that

```text
d_TV(Γ, Γ̂) = η,        H(Γ̂) ≤ H(Γ) + c_* η.
```

Total variation is `sup |Γ(A) − Γ̂(A)|`. The distance `η` is the least possible to a compatible coupling, because every compatible coupling puts mass zero on `B`. The coefficient does not depend on the horizon or on the number of policies.

The good part of `Γ` is a subflow `q ≤ p` of mass `1 − η`. The residual `r = p − q` is a nonnegative flow of root mass `η`. Normalising it and deleting zero branches gives a finite controlled tree, and `Γ(· | B)` is a coupling of its policy marginals. Its envelope entropy is at most `H(Γ(· | B))`, so the checked Shannon bound supplies a compatible replacement `Λ` with `H(Λ) ≤ H(Γ(· | B)) + c_*`. The mixture of the good part with weight `η` on `Λ` is `Γ̂`. Membership of a tuple in `B` is a function of the tuple, so

```text
H(Γ) = h₂(η) + (1 − η) H(Γ(· | Bᶜ)) + η H(Γ(· | B)),
```

and the binary entropy cancels against the mixture bound. The mixture step is an inequality. The chain rule for `H(Γ)` is an equality.

Consequently, for every coefficient `κ ≥ c_*`,

```text
C = min over couplings Γ of [ H(Γ) + κ Γ(B) ].
```

The minimum runs over all couplings of the policy transcripts, with no compatibility restriction. It is attained by an exact causal seed. The identity is not special to `κ = c_*`. What `c_*` supplies is that the coefficient is large enough. For every `λ > c_*`, every minimiser of `H(Γ) + λ Γ(B)` is compatible: an inconsistent candidate would be strictly improved by the repair. The strict separation below this coefficient is not argued here.

## The exact penalty

We assume this reduction is already known. It is not claimed as a discovery. Let `M(T)` be the least entropy of an ordinary coupling of the policy transcripts, and

```text
G_* = sup over finite controlled trees T of (C(T) − M(T)).
```

The checked Shannon bound gives `G_* ≤ c_*`. In Lean that is `CausalSpectrum.gapSup_le_shannonOverhead`: `gapSup` is this supremum and `shannonOverhead` is `c_*`.

`CausalSpectrum.entropy_ge_envelope` is the coupling form of the envelope. Every joint law of the deterministic transcripts, compatible or not, has entropy at least `envelopeMean`. A positive atom is no heavier than any transcript it selects, so its self-information dominates that transcript, and the layer-cake integral of the joint is at least `1 − F⋆`. The ordinary minimum is therefore at least the envelope, and the greedy seed pushed onto its realised transcripts is a compatible coupling of entropy at most `L + c_*`. That is why the gap cannot exceed `c_*`.

`CausalSpectrum.penalty_shortfall` says that no nonnegative coefficient strictly below `gapSup` is universal. If `0 ≤ κ < gapSup`, some tree has penalised infimum strictly smaller than its causal minimum.

The identity is checked for every coefficient at least `gapSup`. `CausalSpectrum.causalMin_le_penalised` says that every coupling satisfies `causalMin T ≤ H(Γ) + gapSup · Γ(B)`. The endpoints `Γ(B) ∈ {0, 1}` are `causalMin_le_penalised_of_zero` and `causalMin_le_penalised_of_one`. The intermediate mass deletes the compatible part (`residualField` in `CausalSeed/Close.lean`), prunes the zero branches (`prunedTree` in `CausalSeed/Transport.lean`), and pays `gapSup` on that tree. `CausalSpectrum.penaltyMin_eq_causalMin` is the equality

```text
C(T) = inf over Γ of [ H(Γ) + κ Γ(B) ]
```

for every `κ ≥ gapSup`, and therefore for every `κ ≥ c_*`. The statement that every minimiser at a penalty strictly above `G_*` is compatible is not a separate theorem.

A stated witness gives `2/9 ≤ G_*`. The search that produced it is not in this repository and was not rerun here. Nothing in the Lean development depends on that number. The interval recorded from that computation remains

```text
2/9 ≤ G_* ≤ (1 + log₂ e) / 2.
```





## What is new

An ordinary minimum-entropy coupling assigns one joint law to a fixed finite list of marginals. It does not, by itself, give a decoder that realises the prescribed kernel at every history and every requested action, including actions that are never taken on the realised branch. The theorem produces that decoder. One finite list of weights is exact for every deterministic policy at once, and the information excess over the adaptive envelope is bounded by a single exponential, uniformly in the horizon.

The size of the exponential is not new. Mean `log₂ e` is the greedy-coupling scale of [Compton, ISIT 2022](https://arxiv.org/abs/2203.05108). The integrated constant `(1 + log₂ e) / 2` is the constant of [Compton, Katz, Qi, Greenewald and Kocaoglu, AISTATS 2023](https://proceedings.mlr.press/v206/compton23a.html) for arbitrarily many marginals. This repository does not improve either number. The lower bound is the information-spectrum converse in the sense of [Shkel and Yadav, ISIT 2023](https://arxiv.org/abs/2305.05745), proved here for deterministic-policy transcripts on the tree. The new statement is the compatible seed, not a new constant.

In Lean the refined integral constant is

```text
shannonOverhead = (1 + 1 / Real.log 2) / 2,
```

which equals `(1 + log₂ e) / 2`, because `Real.log` is the natural logarithm.

## What else is checked

Two identities lie in the same import closure. They are corollaries of the same seed, not a second theorem.

- `wasserstein_gap`: the Wasserstein-1 distance between the law of the seed information and the law of the envelope equals `H − L`.
- `memory_min_entropy`: the min-entropy of one kernel repeated `n` times is the bottleneck recursion. At order `∞` the compatibility gap is zero.

The table below records the remaining finite statements in the closure.

## Not part of the theorem

[`causal_spectrum.pdf`](causal_spectrum.pdf) also states a square-root asymptotic for memoryless actions of equal entropy `h` and varentropies `σᵢ`, with `a = max σᵢ` and `b = min σᵢ`:

```text
C_n^causal = n h + √(2/π) (a − b) √n + o(√n).
```

That asymptotic is argued in the note. It is not the theorem of this repository, and it is not what the Lean development checks. [`CausalSeed/SecondOrder.lean`](CausalSeed/SecondOrder.lean) proves only the mean of profile (13), namely `√(2/π) (a − b)`, including `b = 0 < a`, and the fact that an additive gap of at most `c⋆` does not change a `√n` coefficient. The identification `Gₙ(x√n) → F` is not formalised here. Neither are the Fan–Grama–Liu logarithm, the rigidity statement that needs that limit, nor any claim that `c⋆` is optimal.

The PDF files are the written note. The checked statement is `causal_realization`.

## Where to read

| What | Where |
| --- | --- |
| The theorem | `CausalSpectrum.causal_realization` in `CausalSeed/Entropy.lean` |
| The `(1 − ε)`-support prefix, assumed known, not formalised | section Separate compressions, one prefix |
| Repair by a linear penalty. The infimum identity is checked; the total-variation reconstruction in the section is not a separate theorem | `CausalSeed/Identity.lean`; section Repair of an inconsistent coupling |
| Exact penalty `G_*`: the envelope, the gap, the shortfall, and `penaltyMin κ = causalMin` for `κ ≥ gapSup`. A strict minimiser above `G_*` is not a separate theorem | `CausalSeed/Penalty.lean`, `CausalSeed/Identity.lean`; section The exact penalty |
| The Shannon integral | `CausalSpectrum.one_seed_shannon` in the same file |
| The seed, the policies, the envelope | `CausalSeed/Spectrum.lean`, `CausalSeed/Gap.lean` |
| The Wasserstein identity, min-entropy, Rényi scalars | `CausalSeed/Note.lean` |
| Profile mean and the `√n` transfer only | `CausalSeed/SecondOrder.lean` |
| Axiom audit | [`AXIOMS.txt`](AXIOMS.txt) |
| The note, including arguments not checked here | [`causal_spectrum.pdf`](causal_spectrum.pdf), [`one_seed_entropy.pdf`](one_seed_entropy.pdf) |

## The theorem, as formalised

For every finite controlled tree `T` there is a finite list of atoms, produced by greedy extraction of the probability flow, such that

- the list is a greedy trace of the root probability field,
- every atom weight is strictly positive and at most 1,
- the weights sum to 1,
- under every deterministic policy, the decoder’s transcript weights equal the prescribed leaf masses on the histories compatible with that policy, and equal 0 on the others,
- for every real `t`, `seedCDF t ≤ F⋆(t)` and `seedTail t ≤ coupleSurv t`.

The first comparison is `Z ≼_st J`. The second is `J ≼_st Z + E` for `E ~ Exp(ln 2)`. Integrating it gives `L ≤ H ≤ L + log₂ e`. The separate declaration `one_seed_shannon` is that integral with the constant sharpened to `(1 + log₂ e) / 2`.

`L` is `envelopeMean`, the finite sum that defines the envelope. `Z` is that same envelope, read as a distribution function.

A tree is a leaf, or a node with a positive finite number of actions. Each action has its own positive finite output alphabet and a kernel of strictly positive real weights summing to 1. Alphabets may differ from node to node and from action to action. A policy chooses one action from the whole history and continues along every output. A strategy chooses one output of every action. The same finite seed is exact for every policy.

## Certificate

Checked with Lean `4.35.0-rc3` (`leanprover/lean4:v4.35.0-rc3`) and mathlib `7d6757bc18680044fc0ff6efc8ee20494b408556`, by `lake build` of this import closure. There is no `sorry` and no `admit`.

`#print axioms CausalSpectrum.causal_realization` reports only

```text
propext
Classical.choice
Quot.sound
```

The same three axioms are reported for every declaration below. They are the kernel of Lean, not unproved lemmas.

### The seed and the sandwich

| Step | Declaration |
| --- | --- |
| Stochastic realization, `Z ≼ J ≼ Z + Exp(ln 2)` | `CausalSpectrum.causal_realization` |
| Truncation, `Pr(J > t + s) ≤ Pr(Z > t) + 2^{−s}` | `CausalSpectrum.causal_truncation` |
| Minimax identity for an arbitrary real field | `CausalSpectrum.exact_tree_minimax` |
| Greedy extraction ends and gives one exact seed | `CausalSpectrum.exact_finite_seed` |
| Existence of the greedy trace | `CausalSpectrum.greedyTrace_exists` |
| Residual mass after the cutoff `δ` | `CausalSpectrum.greedy_refined_bound` |
| Exact seed together with the refined cutoffs | `CausalSpectrum.exact_seed_with_refined_cutoffs` |
| Shannon sandwich, the integral, with the refined constant | `CausalSpectrum.one_seed_shannon` |

### Identities in the same closure

| Step | Declaration |
| --- | --- |
| `W₁` equals the entropy gap | `CausalSpectrum.wasserstein_gap` |
| `E[W] = c⋆` and `c⋆ < log₂ e` | `integral_wSurvival`, `shannonOverhead_lt_logb_exp` |
| Strict gap on one finite tree | `CausalSpectrum.finite_gap_strict` |
| Laplace identity and the Rényi scalars `θ₂`, `g̃₂` | `exp_moment`, `theta_two`, `gTilde_two` |
| Min-entropy of a kernel repeated `n` times | `memory_min_entropy` |
| Rational brackets of the crash pair | `crash_lower_pow`, `crash_C_bound` |
| Entropy of the masses `1/3`, `1/3`, `1/6`, `1/6` | `vertex_mass_entropy` |

### Calculations that do not prove the square-root asymptotic

| Step | Declaration |
| --- | --- |
| `∫₀^∞ (1 − Φ(t/c)) dt = c/√(2π)` | `integral_gaussTail`, `integral_normalTail_scale` |
| Mean of profile (13), including `b = 0` | `profile_mean`, `profile_mean_zero` |
| A gap of at most `c⋆` does not change a `√n` coefficient | `second_order_transfer` |

## Build

This archive does not contain mathlib. From this directory, with `elan`:

```text
lake build
```

Lake reads `lean-toolchain` and `lake-manifest.json` and fetches the pinned mathlib revision. The first build downloads the dependencies. Later builds reuse them.

