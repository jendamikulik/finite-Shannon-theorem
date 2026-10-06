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

`coupleSurv t` is `∑ μᵢ min(1, 2^(zᵢ − t))`, which is `P(Z + E > t)` for `E` independent of `Z`. The same seed works at every horizon. Nothing in the gap depends on the depth of the tree.

Integrating the tails gives `L ≤ H ≤ L + log₂ e`. The declaration `CausalSpectrum.one_seed_shannon` is that integral with the residual-mass refinement

```text
L ≤ H ≤ L + (1 + log₂ e) / 2.
```

The refinement sharpens the integral. It does not replace the stochastic bound by a smaller exponential.

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

