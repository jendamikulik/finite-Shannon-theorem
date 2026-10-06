# An exact causal seed on a finite controlled tree

Jan Mikulik, 5 October 2026.

The result of this repository is one theorem, `CausalSpectrum.causal_realization`, in [`CausalSeed/Entropy.lean`](CausalSeed/Entropy.lean).

For every finite controlled history tree, greedy extraction produces one finite seed which is an exact decoder for every deterministic policy. Let `Z` be the information of the lower envelope of the deterministic-policy transcript laws, and let `J` be the information of the seed. Then

```text
Z  ≼_st  J  ≼_st  Z + E,        E ~ Exp(ln 2).
```

In the formalization the two comparisons are, for every real `t`,

```text
seedCDF t ≤ F⋆(t)
seedTail t ≤ coupleSurv t
```

`coupleSurv t` is `∑ μᵢ min(1, 2^(zᵢ − t))`, the survival function of `Z + E` when `E` is exponential of rate `ln 2` and independent of `Z`. The gap does not grow with the horizon.

Integrating the tails gives `L ≤ H ≤ L + log₂ e`. The checked Shannon statement `CausalSpectrum.one_seed_shannon` is the same comparison after integration, with the residual-mass refinement of the constant:

```text
L ≤ H ≤ L + (1 + log₂ e) / 2.
```

That refinement improves the integral. It is not a stronger stochastic bound than `E`. The lower bound is the information-spectrum converse for this family of transcript laws. The upper bound is one seed, consistent at every shared history–action node.

## What is new, and what is not

An ordinary minimum-entropy coupling assigns a joint law to a fixed finite family of marginals. By itself it does not provide a decoder that realises the prescribed kernel at every history and every requested action of a controlled tree. The theorem supplies that compatibility.

The additive constant is not new. It is the constant obtained by Compton, Katz, Qi, Greenewald and Kocaoglu for the Shannon entropy of a greedy coupling of arbitrarily many marginals [(AISTATS 2023, PMLR 206, 10445–10469)](https://proceedings.mlr.press/v206/compton23a.html). This repository does not improve it. The coarser comparison with an exponential of mean `log₂ e` is the scale already known for greedy coupling [(Compton, ISIT 2022)](https://arxiv.org/abs/2203.05108); the factor `1/2` is the residual-mass refinement of the 2023 paper, transferred to the tree. The spectrum lower bound is the viewpoint of Shkel and Yadav [(ISIT 2023)](https://arxiv.org/abs/2305.05745), applied to deterministic-policy transcripts and reproved for this model.

In Lean the constant is

```text
shannonOverhead = (1 + 1 / Real.log 2) / 2,
```

which equals `(1 + log₂ e) / 2`, because `Real.log` is the natural logarithm.

## What else is checked

Two identities lie in the same import closure. They are not a second theorem.

- `wasserstein_gap`: the Wasserstein-1 distance between the law of the seed information and the law of the envelope equals `H − L`.
- `memory_min_entropy`: the min-entropy of one kernel repeated `n` times is the bottleneck recursion.

The table below records the remaining finite statements in the closure, including the Rényi scalars, the strict gap on one finite tree, and the rational brackets for the crash pair.

## What this repository does not prove

[`causal_spectrum.pdf`](causal_spectrum.pdf) also states a square-root asymptotic for a fixed finite family of memoryless action laws of equal entropy `h` and varentropies `σᵢ`, with `a = max σᵢ` and `b = min σᵢ`:

```text
C_n^causal = n h + √(2/π) (a − b) √n + o(√n).
```

That asymptotic is not a theorem of this repository. [`CausalSeed/SecondOrder.lean`](CausalSeed/SecondOrder.lean) proves only the two calculations that do not use the Bellman limit: the mean of profile (13) in the note equals `√(2/π) (a − b)`, including the case `b = 0 < a`, and an additive gap of at most `c⋆ = (1 + log₂ e) / 2` does not change a `√n` coefficient. Once an envelope mean has that second order, every seed between the envelope and the envelope plus `c⋆` has it too. The identification `Gₙ(x√n) → F` is not formalised. Neither are the Fan–Grama–Liu logarithmic bound, the rigidity and moment statements that depend on that limit, nor any claim that `c⋆` is optimal.

The two PDF files are the written note. The checked statement is the Lean theorem.

## Where to read

| What | Where |
| --- | --- |
| The theorem | `CausalSpectrum.causal_realization` in `CausalSeed/Entropy.lean` |
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

`L` is `envelopeMean`, the finite sum that defines the envelope in the written proof. `Z` in the stochastic statement is the same envelope, read as a distribution function, not an extra hypothesis.

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
| Minimax identity for an arbitrary real field | `CausalSpectrum.exact_tree_minimax` |
| Greedy extraction ends and gives one exact seed | `CausalSpectrum.exact_finite_seed` |
| Existence of the greedy trace | `CausalSpectrum.greedyTrace_exists` |
| Residual mass after the cutoff `δ` | `CausalSpectrum.greedy_refined_bound` |
| Exact seed together with the refined cutoffs | `CausalSpectrum.exact_seed_with_refined_cutoffs` |
| Stochastic realization, `Z ≼ J ≼ Z + Exp(ln 2)` | `CausalSpectrum.causal_realization` |
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
