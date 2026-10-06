# One seed — Lean certificate

Jan Mikulik, 5 October 2026.

This archive checks the finite identities from the 5 October 2026 note,
and the second-order coefficient of Theorem 1 as far as it does not use
the Bellman limit. `CausalSeed/SecondOrder.lean` proves that the mean of
profile (13) is `√(2/π) (a − b)`, including the half-normal case `b = 0`,
and that an additive gap of at most `c⋆` does not change a `√n`
coefficient. The identification `Gₙ(x√n) → F` (Lemmas 10–13), the
Fan–Grama–Liu logarithm, the rigidity and moment statements that ride on
that limit, and any claim that `c⋆` is optimal are not in these files.

## Written notes

Two notes accompany the certificate:

- [causal_spectrum.pdf](causal_spectrum.pdf) defines the controlled tree, policies, strategies, and the greedy extraction of the probability flow.
- [one_seed_entropy.pdf](one_seed_entropy.pdf) derives the Shannon sandwich and the constant `(1 + log₂ e) / 2`.

These notes are explanatory. The checked statement is the Lean theorem below.

## The theorem

`CausalSpectrum.one_seed_shannon` (in `CausalSeed/Entropy.lean`):

For every finite controlled tree `T` there is a finite list of atoms,
produced by greedy extraction of the probability flow, such that

- the list is a greedy trace of the root probability field,
- every atom weight is strictly positive and at most 1,
- the weights sum to 1,
- under every deterministic policy, the decoder’s transcript weights
  equal the prescribed leaf masses on the histories compatible with
  that policy, and equal 0 on the others,
- if `H` is the Shannon entropy of those weights and `L` is the mean of
  the lower envelope of the policy information c.d.f.s, then

```
L ≤ H ≤ L + (1 + log₂ e) / 2.
```

The overhead is defined as

```
shannonOverhead = (1 + 1 / Real.log 2) / 2,
```

which is exactly `(1 + log₂ e) / 2`, since `Real.log` is the natural
logarithm.

## What was checked

- Lean `4.35.0-rc3` (`leanprover/lean4:v4.35.0-rc3`)
- mathlib `7d6757bc18680044fc0ff6efc8ee20494b408556`
- `lake build` of this import closure
- no `sorry`, no `admit`, and no extra mathematical axioms

`#print axioms CausalSpectrum.one_seed_shannon` reports only

```
propext
Classical.choice
Quot.sound
```

The same three axioms are reported for the supporting declarations below.
They are the standard logical kernel of Lean, not unproved lemmas.

## Manuscript step → declaration

| Step | Declaration |
| --- | --- |
| Minimax identity for an arbitrary real field | `CausalSpectrum.exact_tree_minimax` |
| Greedy extraction ends and gives one exact seed | `CausalSpectrum.exact_finite_seed` |
| Existence of the greedy trace | `CausalSpectrum.greedyTrace_exists` |
| Residual mass after the cutoff `δ` | `CausalSpectrum.greedy_refined_bound` |
| Exact seed together with the refined cutoffs | `CausalSpectrum.exact_seed_with_refined_cutoffs` |
| Shannon sandwich, envelope mean plus the constant | `CausalSpectrum.one_seed_shannon` |
| `W₁` equals the entropy gap | `CausalSpectrum.wasserstein_gap` |
| `E[W] = c⋆` and `c⋆ < log₂ e` | `integral_wSurvival`, `shannonOverhead_lt_logb_exp` |
| Strict gap on one finite tree | `CausalSpectrum.finite_gap_strict` |
| Laplace identity and the Rényi scalars `θ₂`, `g̃₂` | `exp_moment`, `theta_two`, `gTilde_two` |
| Min-entropy of a kernel repeated `n` times | `memory_min_entropy` |
| Rational brackets of the crash pair | `crash_lower_pow`, `crash_C_bound` |
| Entropy of the masses `1/3, 1/3, 1/6, 1/6` | `vertex_mass_entropy` |
| `∫₀^∞ (1 − Φ(t/c)) dt = c/√(2π)` | `integral_gaussTail`, `integral_normalTail_scale` |
| Mean of profile (13), including `b = 0` | `profile_mean`, `profile_mean_zero` |
| Gap at most `c⋆` does not change the `√n` coefficient | `second_order_transfer` |

`L` in the theorem is `envelopeMean`, the finite sum that defines the
envelope in the written proof. It is not an appeal to an abstract law `Z`.

## Build

The archive does not contain mathlib. From this directory, with `elan`:

```
lake build
```

Lake reads `lean-toolchain` and `lake-manifest.json` and fetches the pinned
mathlib revision. The first build downloads the dependencies; later builds
reuse them.

## Model, as formalized

A tree is a leaf, or a node with a positive finite number of actions.
Each action has its own positive finite output alphabet and a kernel of
strictly positive real weights summing to 1. Alphabets may differ from
node to node and from action to action. A policy chooses one action from
the whole history and continues along every output. A strategy chooses one
output of every action. The same finite seed is exact for every policy.
