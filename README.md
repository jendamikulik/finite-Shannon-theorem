# One seed — Lean certificate

Jan Mikulik, 5 October 2026.

This archive is the import closure of one theorem. It is not the whole
manuscript. The square-root asymptotic, the Rényi bounds, the W₁ identity,
and any claim that the constant 1.221347… is optimal are not in these files.

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
