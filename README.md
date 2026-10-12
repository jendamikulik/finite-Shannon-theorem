# One Seed for Every Adaptive Policy

**Exact causal simulation on controlled trees, formalized in Lean 4.**

Jan Mikulík

## Abstract

A controlled tree is a finite or locally finite game in which a policy picks an
action at each history and the environment answers with a random output drawn from
a kernel attached to that history and action. A *causal seed* is one random variable
together with a deterministic response strategy for every value. At every history and
action, all policies that reach that history see the same response. The seed is
*exact* if, under every deterministic adaptive policy, the resulting transcript has
exactly the prescribed law.

This repository proves in Lean 4 that the least entropy of an exact causal seed is
governed by one object: the lower envelope $`F^{\ast}`$ of the transcript-information CDFs
over all policies, and its mean $`L`$. Results:

- For finite trees, the optimal entropy is within the universal constant
  $`c_{\star}=\tfrac12(1+\log_2 e)`$ of $`L`$.
- The bound extends to infinite horizons, to atomic capacity and to Rényi entropies of
  every positive order, also when kernels have zero entries.
- For stationary kernels this gives the sharp $`\sqrt n`$ asymptotic, its $`W_1`$
  universality, and the linear growth rate when the actions' entropies differ.
- For dyadic kernels the overhead vanishes. With one uniform action, the optimal cost is an
  exact random-walk maximum, given by Spitzer's identity.

Every result listed below is checked by the Lean kernel, with no `sorry` and no
axioms beyond Lean's standard three.

## Contents

1. [Setting and notation](#setting-and-notation)
2. [Main results](#main-results)
3. [Verification](#verification)
4. [Trusted definitions](#trusted-definitions)
5. [Repository layout](#repository-layout)
6. [Scope and open problems](#scope-and-open-problems)
7. [Attribution](#attribution)

## Setting and notation

- **Trees.** A finite controlled tree (`Tree`) has, at each node, finitely many
  actions and, for each action $`a`$, finitely many outputs $`y`$ with kernel
  $`K_a(y)>0`$ and $`\sum_y K_a(y)=1`$. A locally finite infinite tree (`ITree`) assigns
  such a finite positive kernel to every history. `trunc ι n []` is its depth-$`n`$
  truncation. A stationary kernel (`Kernel`) repeats one finite family of positive
  laws $`(K_a)_a`$ for $`n`$ rounds (`Kernel.rounds n`).
- **Policies and seeds.** Policies are deterministic and adaptive. A strategy fixes
  a response for every action at every history, including histories it never
  visits. A finite seed is a weighted list of strategies. A countable seed is a
  countable law on strategies of the infinite tree. It is exact to horizon $`n`$ if
  every history of length at most $`n`$ receives its path probability.
- **Information and envelope.** For a transcript $`\ell`$ of probability $`p(\ell)`$,
  $`I(\ell)=-\log_2 p(\ell)`$. For a policy $`\pi`$, $`F_\pi(t)=\Pr_\pi[I\le t]`$. The
  envelope is $`F^{\ast}(t)=\min_\pi F_\pi(t)`$, with mean
  $`L=\int_0^\infty(1-F^{\ast}(t))\,dt`$. On an infinite tree, $`L_n`$ is the mean at horizon
  $`n`$, $`L_\infty=\sup_nL_n`$ and $`F_\infty(t)=\inf_nF^{\ast}_n(t)`$.
- **Costs.** $`C(T)`$ is the least entropy of an exact causal coupling of a finite tree.
  $`C_n`$ is the least entropy of a countable seed exact to horizon $`n`$, and $`C_\infty`$
  the least entropy of a seed exact at every horizon.
- **Units.** All entropies in the statements below are in **bits**. In Lean, the
  countable-seed entropies `CountableSeed.entropy`, `finiteCost` and `infiniteCost`
  are in nats; `Kernel.costBits` and `countableInfiniteCostBits` convert to bits.
  The convention is $`0\log0=0`$. Infinite optima take values in $`[0,\infty]`$.

The constants are

```math
c_\star=\frac{1+\log_2 e}{2}\approx 1.2213475204,
\qquad
d_\alpha=\frac{\log_2\!\bigl(\tfrac12+\tfrac{2^{-\alpha}}{\alpha}\bigr)}{1-\alpha}\ \ (\alpha\ne1),
\qquad d_1=c_\star .
```

## Main results

Unless a sub-namespace is shown, Lean names are in namespace `CausalSpectrum`.

### I. Finite trees

**Theorem 1 (one seed, Shannon sandwich).** For every finite controlled tree $`T`$
there is a finite exact causal seed $`S`$, produced by a greedy bottleneck procedure,
with

```math
L(T)\;\le\;H(S)\;\le\;L(T)+c_\star .
```

Every exact coupling, causal or not, has entropy at least $`L(T)`$, so
$`L(T)\le C(T)\le L(T)+c_{\star}`$.

Lean:
- [`one_seed_shannon`](CausalSeed/Entropy.lean#L1767)
- [`entropy_ge_envelope`](CausalSeed/Penalty.lean#L333)
- [`ordinaryMin_ge_envelope`](CausalSeed/Penalty.lean#L660)
- [`causalMin_le_overhead`](CausalSeed/Penalty.lean#L666)

**Theorem 2 (causal realization).** The same seed is stochastically sandwiched:
$`F_S(t)\le F^{\ast}(t)`$ for all $`t`$, together with an explicit upper comparison of its
survival function. For every exact finite seed,

```math
\int_0^\infty |F^*(t)-F_S(t)|\,dt = H(S)-L(T).
```

Lean:
- [`causal_realization`](CausalSeed/Entropy.lean#L2008)
- [`seedCDF_le_Fstar`](CausalSeed/Entropy.lean#L1703)
- [`wasserstein_gap`](CausalSeed/Gap.lean#L55)

**Theorem 3 (zero-probability branches).** Let the kernels be nonnegative and
normalized, so that zero-probability branches are kept in the tree (`Zero.ZTree`).
There is a law $`q`$ on total strategies that is exact for every policy and satisfies
$`L\le H(q)\le L+c_{\star}`$. Every exact law has $`H(q)\ge L`$.

Lean:
- [`Zero.zero_closure`](CausalSeed/ZeroClosure.lean#L130)
- [`Zero.zero_lower`](CausalSeed/ZeroClosure.lean#L154)

**Theorem 4 (dyadic exactness).** Suppose every kernel entry is a power of $`1/2`$.
Then some exact finite seed with dyadic atoms has $`F_S=F^{\ast}`$, hence $`H(S)=L(T)`$, and
there is no overhead. For a stationary dyadic kernel,

```math
C_n = L_n\qquad\text{for every } n .
```

The key step, `Dyadic.couple`, is a comonotone refinement. Finitely many dyadic laws
of mass one have a common dyadic refinement whose information CDF is at least the
minimum of theirs.

Lean:
- [`Dyadic.dyadic_exact`](CausalSeed/DyadicTree.lean#L184)
- [`Kernel.cost_eq_envelope_of_dyadic`](CausalSeed/DyadicKernel.lean#L139)
- [`Dyadic.couple`](CausalSeed/DyadicCouple.lean#L254)
- [`Completion.finiteCost_le_atoms`](CausalSeed/DyadicKernel.lean#L117)

### II. Infinite horizons and atomic capacity

Let $`\iota`$ be a locally finite infinite tree with positive kernels.

**Theorem 5 (projective identity and attainment).** In nats,
$`C_\infty=\sup_n C_n`$. If this value is finite, it is attained by one countable seed
exact at every horizon.

Lean:
- [`Completion.projective_entropy_identity`](CausalSeed/EntropyLimit.lean#L351)
- [`Completion.entropy_attained`](CausalSeed/EntropyLimit.lean#L309)

**Theorem 6 (infinite sandwich).** For countable seeds exact at every horizon, in bits,

```math
L_\infty \;\le\; C_\infty \;\le\; L_\infty + c_\star ,
```

and, whenever $`L_\infty<\infty`$, an exact seed attains $`C_\infty`$. In particular, an
exact seed of finite entropy exists if and only if $`\sup_n L_n<\infty`$.

Lean:
- [`Completion.infinite_envelope_sandwich`](CausalSeed/InfiniteEnvelope.lean#L60)
- [`Completion.infinite_envelope_attained`](CausalSeed/InfiniteEnvelope.lean#L82)
- [`Completion.infiniteCost_lt_top_iff`](CausalSeed/EnvelopeBridge.lean#L395)

**Theorem 7 (atomic capacity).** Let $`\mathrm{atomQ}=\sup_K\inf_{n,\pi}A_K(P_{n,\pi})`$,
where $`A_K`$ is the total mass of the $`K`$ heaviest transcripts. Then:

1. Every ordinary exact source, causal or not, has atomic mass at most
   $`\mathrm{atomQ}`$.
2. Some exact causal probability measure on strategies has atomic mass exactly
   $`\mathrm{atomQ}`$.
3. An exact countably supported causal seed exists if and only if $`\mathrm{atomQ}=1`$.
4. The capacity is read off the envelope:

```math
\mathrm{atomQ}=\lim_{t\to\infty}F_\infty(t)=\sup_t F_\infty(t).
```

Lean:
- [`Completion.ordinary_atomic_upper`](CausalSeed/AtomicCapacity.lean#L76)
- [`Completion.causal_atomic_capacity_attained`](CausalSeed/AtomicCapacity.lean#L147)
- [`Completion.countable_seed_iff_atomQ_one`](CausalSeed/AtomicCapacity.lean#L216)
- [`atomQ_eq_lim_FInf`](CausalSeed/AtomicSpectrum.lean#L118)
- [`atomQ_eq_iSup_FInf`](CausalSeed/AtomicSpectrum.lean#L134)

### III. One seed for the whole Rényi spectrum

Let $`\iota`$ be as in Section II.

- An *ordinary exact source* (`RenyiInf.OrdSource`) is a countable law with, for each
  horizon, a deterministic readout of a joint transcript. Its readouts need not be
  history-consistent or consistent across horizons.
- $`O_\alpha`$ and $`C_\alpha`$ are the infima of $`H_\alpha`$ over ordinary and over
  causal exact sources.
- $`Z`$ is the envelope limit variable, a law on $`[0,\infty]`$ with CDF $`F_\infty`$ and an
  atom of mass $`1-\mathrm{atomQ}`$ at $`+\infty`$.
- $`R_\alpha(Z)`$ is the Rényi functional of the law of $`Z`$:
  $`(1-\alpha)^{-1}\log_2\mathbb E\,2^{(1-\alpha)Z}`$ for $`\alpha\ne1`$ and $`\mathbb EZ`$ for
  $`\alpha=1`$.

**Theorem 8.** Suppose an ordinary exact source exists. Then there is one countable
causal seed $`S`$, exact at every horizon, such that for every $`\alpha>0`$

```math
R_\alpha(Z)\;\le\;O_\alpha\;\le\;C_\alpha\;\le\;H_\alpha(S)\;\le\;R_\alpha(Z)+d_\alpha ,
```

and for the min-entropy

```math
H_\infty(S)=C_\infty^{\mathrm R}=O_\infty^{\mathrm R}.
```

At each order, $`O_\alpha`$, $`C_\alpha`$, $`R_\alpha(Z)`$ and $`H_\alpha(S)`$ are finite or
infinite together. Examples: $`d_1=c_{\star}`$ and $`d_2=\log_2(8/5)`$.

Lean:
- [`RenyiInf.one_seed_all_orders_meas`](CausalSeed/RenyiLimitMeasure.lean#L350)
  (with $`R_\alpha(Z)`$ computed from the measure `lawZ`)
- [`RenyiInf.one_seed_all_orders`](CausalSeed/RenyiInfinite.lean#L202)
- [`RenyiInf.RZmeas_eq`](CausalSeed/RenyiLimitMeasure.lean#L337)
  ($`R_\alpha(Z)=\sup_nR_\alpha(Z_n)`$)
- [`RenyiInf.simultaneous_finiteness`](CausalSeed/RenyiInfinite.lean#L232)

### IV. Stationary kernels

Let a finite family of positive laws $`(K_a)_a`$ be used at every round. Put
$`X_a=-\log_2K_a(Y)`$ for $`Y\sim K_a`$, and let $`C_n`$ and $`L_n`$ be the optimal cost and
the envelope mean at horizon $`n`$, in bits.

**Theorem 9 (sharp square-root asymptotic).** Suppose all actions have the same
entropy $`h=\mathbb E X_a`$. Put $`a=\max_a\sigma_a`$ and $`b=\min_a\sigma_a`$, where
$`\sigma_a^2=\mathrm{Var}X_a`$. Then

```math
C_n = nh+\sqrt{\tfrac{2}{\pi}}\,(a-b)\sqrt n+o(\sqrt n),
```

and the same holds for $`L_n`$. It also holds for the entropy of any exact finite
seeds $`S_n`$ with $`L_n\le H(S_n)\le L_n+c_{\star}`$, which includes the greedy seeds.

If $`b>0`$, there is a constant $`K`$ such that for all $`n\ge3`$

```math
\Bigl|C_n-nh-\sqrt{\tfrac{2}{\pi}}\,(a-b)\sqrt n\Bigr|\le K\,n^{1/4}\log n ,
```

and the same bound holds for the greedy seed.

Lean:
- [`Kernel.cost_tendsto`](CausalSeed/SqrtGeneral.lean#L384)
- [`Kernel.envelope_tendsto`](CausalSeed/SqrtGeneral.lean#L376)
- [`Kernel.greedy_tendsto`](CausalSeed/SqrtGeneral.lean#L391)
- [`Kernel.cost_rate`](CausalSeed/SqrtMain.lean#L122)
- [`Kernel.greedy_rate`](CausalSeed/SqrtMain.lean#L131)

**Theorem 10 ($`W_1`$ universality).** In the setting of Theorem 9, assume $`a>0`$.
Let $`F_{a,b}`$ be the limit profile:

```math
F_{a,b}(z)=\begin{cases}\dfrac{2b}{a+b}\,\Phi(z/b), & z\le0,\\[2mm]
1-\dfrac{2a}{a+b}\,\Phi(-z/a), & z\ge0,\end{cases}
```

which is the half-normal CDF $`1-2\Phi(-z/a)`$, $`z>0`$, when $`b=0`$. Let $`S_n`$ be
countable seeds, exact to horizon $`n`$, with finite entropy and with
$`H(S_n)-C_n=o(\sqrt n)`$. Let $`J_n`$ be the information of $`S_n`$. Then

```math
\int_{\mathbb R}\Bigl|\Pr\!\Bigl[\tfrac{J_n-nh}{\sqrt n}\le x\Bigr]-F_{a,b}(x)\Bigr|\,dx\;\longrightarrow\;0 .
```

The same convergence holds for the optimal-transport distance. Define, for
probability measures on $`\mathbb R`$,

```math
W_1(\mu,\nu)=\inf_{\gamma\in\Pi(\mu,\nu)}\int|x-y|\,d\gamma(x,y)\in[0,\infty],
```

the infimum over all couplings. Then $`W_1(\mu,\nu)=\int_{\mathbb R}|F_\mu-F_\nu|`$, and
the quantile coupling $`(F_\mu^{-1}(U),F_\nu^{-1}(U))`$, $`U`$ uniform on $`(0,1)`$,
attains the infimum; no moment assumption is needed in this extended-valued form.
Consequently $`W_1\bigl(\mathcal L(\tfrac{J_n-nh}{\sqrt n}),\mu_{a,b}\bigr)\to0`$, where
$`\mu_{a,b}`$ is the probability measure with CDF $`F_{a,b}`$. For a finite tree and an
exact finite seed with positive atoms, $`W_1(\mathcal L(J),\mu_{F^\ast})=H(S)-L`$, where
$`\mu_{F^\ast}`$ is the law with CDF $`F^\ast`$. For finite seeds the CDF statement is
`Kernel.universality`. The analytic core is
`Sqrt.IncFamily.L1_tendsto`:
$`\int|G_n(x\sqrt n)-F_{a,b}(x)|\,dx\to0`$ for the Bellman envelope $`G_n`$.

Lean:
- [`Kernel.universality_countable`](CausalSeed/SqrtUniversalityCountable.lean#L182)
- [`Kernel.universality`](CausalSeed/SqrtUniversality.lean#L240)
- [`Sqrt.IncFamily.L1_tendsto`](CausalSeed/SqrtUniversality.lean#L102)
- [`Kernel.universality_W1`](CausalSeed/SqrtW1.lean#L137)
- [`OT.W1_eq_cdfDist`](CausalSeed/Wasserstein.lean#L263)
- [`OT.qCoupling_optimal`](CausalSeed/Wasserstein.lean#L268)
- [`wasserstein_gap_W1`](CausalSeed/GapW1.lean#L85)

**Theorem 11 (causal Shannon floor).** The entropies need not be equal. Let
$`h_{\max}=\max_aH(K_a)`$, $`M=\max_{a,y}|{-\log_2K_a(y)}-h_{\max}|`$ and
$`K=\int_{\mathbb R}e^{-x^2/(2M^2)}\,dx`$. For every $`n\ge1`$,

```math
nh_{\max}-K\sqrt n\;\le\;L_n\;\le\;C_n\;\le\;nh_{\max}+K\sqrt n+c_\star ,
\qquad\text{so}\qquad \frac{C_n}{n}\to h_{\max}.
```

Lean:
- [`Kernel.cost_floor_bounds`](CausalSeed/CausalFloor.lean#L284)
- [`Kernel.causal_floor`](CausalSeed/CausalFloor.lean#L329)
- [`Kernel.envelope_floor`](CausalSeed/CausalFloor.lean#L334)

**Theorem 12 (subadditivity).** For every stationary kernel and all $`m,n`$,

```math
C_{m+n}\;\le\;C_m+C_n .
```

Two seeds exact to horizons $`m`$ and $`n`$ are concatenated: the first answers at
histories of length less than $`m`$, the second at the later rounds, reading the
history from round $`m`$ on. Path masses factor over this split, so the product seed
is exact to horizon $`m+n`$, and its entropy is the sum of the two entropies.

Lean:
- [`Kernel.costBits_subadditive`](CausalSeed/Subadditive.lean#L191) (bits)
- [`Kernel.finiteCost_subadditive`](CausalSeed/Subadditive.lean#L175) (nats)
- [`Kernel.catSeed_exactTo`](CausalSeed/Subadditive.lean#L134)
- [`Kernel.catSeed_entropy`](CausalSeed/Subadditive.lean#L150)

**Theorem 13 (Fekete limit and exact lower bound).** By Fekete's lemma,
$`C_n/n\to\inf_{n\ge1}C_n/n`$. With Theorem 11 this identifies the infimum:

```math
h_{\max}=\inf_{n\ge1}\frac{C_n}{n},
\qquad\text{hence}\qquad
n\,h_{\max}\;\le\;C_n\qquad\text{for every } n\ge1 .
```

Lean:
- [`Kernel.costBits_fekete`](CausalSeed/Subadditive.lean#L210)
- [`Kernel.hmax_eq_inf`](CausalSeed/Subadditive.lean#L217)
- [`Kernel.hmax_mul_le_costBits`](CausalSeed/Subadditive.lean#L222)

**Theorem 14 (kernels with zero entries).** Let $`K_a`$ be nonnegative laws, and let
$`K^{\mathrm{red}}`$ be obtained by deleting the zero entries of every $`K_a`$. Let
$`C_n(K)`$ be the least Shannon entropy (bits) of a law on response strategies of the
$`n`$-round tree that keeps every branch, including those of probability zero, and is
exact for every deterministic adaptive policy. Then the envelope of this tree equals
$`L_n(K^{\mathrm{red}})`$, so

```math
L_n(K^{\mathrm{red}})\;\le\;C_n(K)\;\le\;L_n(K^{\mathrm{red}})+c_\star .
```

Moreover the cost itself is unchanged by the reduction:

```math
C_n(K)=C_n(K^{\mathrm{red}})\qquad\text{for every }n .
```

A strategy of the full tree is restricted to the positive branches, and a strategy of
the reduced tree is extended arbitrarily on the zero branches; pushing an exact law
forward along either map keeps it exact and does not increase its entropy, because
an exact law gives mass zero to strategies that answer with a zero-probability output
along a positive-probability history. For positive kernels the finite-law cost
coincides with the countable-seed cost $`C_n`$ of Theorems 9–13. Hence Theorems 12
and 13 hold for $`K`$: $`C_{m+n}(K)\le C_m(K)+C_n(K)`$, $`C_n(K)/n\to h_{\max}=\inf_{n\ge1}C_n(K)/n`$
and $`n\,h_{\max}\le C_n(K)`$. Also Theorem 11 holds for $`K`$ with $`h_{\max}=\max_a H(K_a)`$ (with $`0\log0=0`$),
and Theorem 9, including the $`O(n^{1/4}\log n)`$ rate when $`b>0`$, holds for $`K`$ with
$`h,a,b`$ computed from $`K^{\mathrm{red}}`$, that is, over the support of each $`K_a`$.

Lean:
- [`Zero.NNKernel.L_ztree`](CausalSeed/ZeroKernel.lean#L184)
- [`Zero.NNKernel.costBits_sandwich`](CausalSeed/ZeroKernel.lean#L222)
- [`Zero.NNKernel.cost_floor_bounds`](CausalSeed/ZeroKernel.lean#L238)
- [`Zero.NNKernel.causal_floor`](CausalSeed/ZeroKernel.lean#L246)
- [`Zero.NNKernel.cost_tendsto`](CausalSeed/ZeroKernel.lean#L251)
- [`Zero.NNKernel.cost_rate`](CausalSeed/ZeroKernel.lean#L270)
- [`Zero.NNKernel.zcost_ztree`](CausalSeed/ZeroCost.lean#L415)
- [`Zero.NNKernel.costBits_eq_red`](CausalSeed/ZeroCost.lean#L429)
- [`Kernel.costBits_eq_tcost`](CausalSeed/ZeroCost.lean#L162)
- [`Zero.NNKernel.costBits_subadditive`](CausalSeed/ZeroCost.lean#L433)
- [`Zero.NNKernel.hmax_eq_inf`](CausalSeed/ZeroCost.lean#L438)
- [`Zero.NNKernel.hmax_mul_le_costBits`](CausalSeed/ZeroCost.lean#L448)

**Theorem 15 (moment classification: square-root branch and logarithmic lower bound).** In the
setting of Theorem 9, if $`a>b`$ there are $`0<c_1\le c_2`$ with
$`c_1\sqrt n\le C_n-nh\le c_2\sqrt n`$ for all large $`n`$; if $`a=b`$, then
$`C_n-nh=o(\sqrt n)`$. Moreover, if two actions $`j,k`$ have centered information
laws with equal variances but different third moments, there is $`c>0`$ with
$$`
c\log n\le L_n-nh\le C_n-nh\qquad\text{for all large } n .
`$$
The proof writes $`L_n-nh=e(G_n)`$, the mean of the law $`\mu_n`$ with CDF $`G_n`$, shows
$`e(G_{n+1})-e(G_n)\ge\tfrac12\int|E_jG_n-E_kG_n|`$, and bounds the integral below by
$`c/n`$ through the identity
$`\int (E_jG_n-E_kG_n)(x)\,e^{itx}\,dx=-\hat\mu_n(t)\,(\varphi_j(t)-\varphi_k(t))/(it)`$
at $`t\asymp n^{-1/2}`$, where $`\varphi_j`$ is the characteristic function of the
centered information of action $`j`$. The same lower bound holds for nonnegative kernels,
stated for the reduced kernel.

Lean:
- [`Kernel.excess_theta_sqrt`](CausalSeed/MomentClass.lean#L20)
- [`Kernel.excess_little_o`](CausalSeed/MomentClass.lean#L36)
- [`Kernel.excess_log_lower`](CausalSeed/MomentLower.lean#L200)
- [`Zero.NNKernel.excess_log_lower`](CausalSeed/MomentLower.lean#L217)
- [`Sqrt.IncFamily.fourier_R`](CausalSeed/MomentFourier.lean#L223),
  [`Sqrt.IncFamily.integral_abs_R_lower`](CausalSeed/MomentFourier.lean#L442),
  [`Sqrt.IncFamily.eG_step`](CausalSeed/MomentLower.lean#L94),
  [`Kernel.envelope_sub_eq_eG`](CausalSeed/MomentLower.lean#L172)

**Theorem 16 (moment classification: logarithmic and bounded branches).** In the setting of
Theorem 9, let $`j_0`$ be an action whose centered information law contains a symmetric
pair of atoms, $`\mu_{j_0}=\rho\,\delta_c*\tfrac12(\delta_{-b}+\delta_b)+\zeta`$ with
$`b>0`$, $`0<\rho\le1`$ and $`\|\zeta\|_{\mathrm{TV}}\le1-\rho`$; every law with two
distinct values has this form. Any finite number of actions is allowed.

1. If every action has the variance of $`j_0`$, there is $`C`$ with
   $`L_n-nh\le C(1+\log n)`$ and $`C_n-nh\le C(1+\log n)+c_{\star}`$ for all $`n\ge1`$.
2. If every action also has the third moment of $`j_0`$, then $`L_n-nh`$ and
   $`C_n-nh`$ are bounded.
3. If all actions have equal variances and two have different third moments, there are
   $`0<c\le C`$ with
$$`
c\log n\le L_n-nh\le C\log n,\qquad c\log n\le C_n-nh\le C\log n
`$$
   for all large $`n`$. No nondegeneracy hypothesis is needed here: a centered law with
   nonzero third moment has two distinct values.

The same bounds hold for nonnegative kernels, stated for the reduced kernel.

The proof bounds $`e(G_n)`$ by the integrated width
$`W_n=\int(U_nG_0-G_n)`$ between the upper and lower policy envelopes, where
$`U_n`$ iterates $`f\mapsto\max_jE_jf`$. Smoothing by $`\Psi=\Psi_6`$, the CDF of a sum
of six independent uniforms on $`[-a,a]`$, gives the recursion
$$`
W_n\le 24a+2\sum_{i<n}\bigl(\alpha_{n-1-i}+\beta_{n-1-i}W_i\bigr),
`$$
where $`\alpha_r`$ and $`\beta_r`$ are the $`L^1`$ norms of
$`(E_j-E_{j_0})(\mu_{j_0}^{*r}*\Psi)`$ and of its derivative. When the moments of
order $`<m`$ agree, a Taylor bound gives
$`\|(E_j-E_{j_0})f\|_{L^1}\le(E|X_j|^m+E|X_{j_0}|^m)\|f^{(m)}\|_{L^1}`$, and
$`f^{(m)}=\mu_{j_0}^{*r}*\Delta_a^{m-1}*\Psi_{7-m}'`$ with $`\Delta_a=(\delta_{-a}-\delta_a)/2a`$.
Total-variation decay of the smoothed walk, $`\|\Delta_b^q*\mu_{j_0}^{*r}\|_{\mathrm{TV}}=O(r^{-q/2})`$
for $`q\le4`$ (binomial mixture and Rademacher orthogonality), makes
$`\sum_r\beta_r\le\tfrac14`$ once $`a`$ is a large multiple of $`b`$, and gives
$`\sum_{r<n}\alpha_r=O(\log n)`$ for $`m=3`$ and $`O(1)`$ for $`m=4`$.

Lean:
- [`Kernel.excess_log_upper`](CausalSeed/MomentAssembly.lean#L420)
- [`Kernel.excess_bdd_upper`](CausalSeed/MomentAssembly.lean#L434)
- [`Kernel.excess_log_theta`](CausalSeed/MomentAssembly.lean#L449)
- [`Zero.NNKernel.excess_log_upper`](CausalSeed/MomentAssembly.lean#L482),
  [`excess_bdd_upper`](CausalSeed/MomentAssembly.lean#L489),
  [`excess_log_theta`](CausalSeed/MomentAssembly.lean#L497)
- [`Sqrt.IncFamily.eG_log_upper`](CausalSeed/MomentAssembly.lean#L299),
  [`eG_bdd_upper`](CausalSeed/MomentAssembly.lean#L349),
  [`nondeg_of_ne`](CausalSeed/MomentAssembly.lean#L224),
  [`nondeg_of_m3_ne_zero`](CausalSeed/MomentAssembly.lean#L400)
- Ingredients: [`lintegral_expect_sub_le`](CausalSeed/MomentTaylor.lean#L139) (Taylor),
  [`Decay.tv_mixture`](CausalSeed/MomentDecay.lean#L365) (TV decay),
  [`Sqrt.IncFamily.polE_abs_le`](CausalSeed/MomentWidth.lean#L274),
  [`WidthData.Wint_le`](CausalSeed/MomentWidth.lean#L558),
  [`recursion_solve`](CausalSeed/MomentWidth.lean#L598),
  [`ofReal_eG_le_Wint`](CausalSeed/MomentUpper.lean#L159)

**Theorem 17 (monotone residual; deterministic images).** For every stationary positive
kernel and every action $`j`$, $`C_{n+1}\ge H(K_j)+C_n`$. Hence the residual
$`C_n-nh_{\max}`$ is nonnegative and nondecreasing, and it converges to a finite limit
whenever it is bounded. If every output law is a deterministic image of one action's law,
$`K_a=(f_a)_\#K_{j_0}`$, then $`H(K_{j_0})=h_{\max}`$ and $`C_n=nh_{\max}`$ for every $`n`$.

The first inequality conditions an exact horizon-$`(n+1)`$ seed on the first output of
action $`j`$; each conditional seed is exact to horizon $`n`$, and the chain rule gives the
bound. The second statement uses one sample of $`K_{j_0}`$ per round, read through
$`f_a`$, together with subadditivity and Theorem 13.

Lean:
- [`Kernel.costBits_succ_ge`](CausalSeed/GapImage.lean#L293)
- [`Kernel.residual_mono`](CausalSeed/GapImage.lean#L306),
  [`residual_nonneg`](CausalSeed/GapImage.lean#L313),
  [`residual_tendsto`](CausalSeed/GapImage.lean#L318)
- [`Kernel.costBits_eq_of_image`](CausalSeed/GapImage.lean#L120),
  with [`Kernel.IsImage`](CausalSeed/GapImage.lean#L19)

**Theorem 18 (zero set of the residual).** For every stationary positive kernel the
following are equivalent: (i) $`C_1=h_{\max}`$; (ii) there are an action $`j_0`$ and maps
$`f_a`$ with $`K_a=(f_a)_\#K_{j_0}`$ for every $`a`$; (iii) $`C_n=nh_{\max}`$ for every $`n`$.
Equivalently, the limit of the residual is $`0`$ if and only if every output law is a
deterministic image of a maximizing law.

An exact horizon-1 seed induces a coupling of the output laws (the tuple of first answers),
and by data processing $`C_1`$ is at least the least entropy of a coupling. The couplings
form a compact set, so this least entropy is attained. A coupling whose entropy does not
exceed $`H(K_{j})=h_{\max}`$ has point-mass conditional laws given the $`j`$-th coordinate
(strict subadditivity of $`-x\log x`$), so the other coordinates are functions of it.

Lean:
- [`Kernel.zero_set`](CausalSeed/GapZero.lean#L223)
- [`Kernel.exists_min_cpl`](CausalSeed/GapZero.lean#L149),
  [`Kernel.finiteCost_one_ge`](CausalSeed/GapZero.lean#L156),
  [`Kernel.image_of_cpl`](CausalSeed/GapZero.lean#L167)
- [`Kernel.residual_bdd_of_subseq`](CausalSeed/GapZero.lean#L255): a bound along any
  unbounded sequence of horizons bounds the residual everywhere.

**Theorem 19 (strict entropy gap: bounded residual).** Let $`\kappa`$ be a stationary
strictly positive kernel in which exactly one action $`j_0`$ attains
$`h_{\max}=\max_a H(K_a)`$, i.e. $`H(K_a)<H(K_{j_0})`$ for every $`a\ne j_0`$. Then there is
a constant $`K`$, independent of $`n`$, with

```math
nh_{\max}\le C_n\le nh_{\max}+K\qquad\text{for all }n .
```

Consequently $`\ell=\lim_{n\to\infty}(C_n-nh_{\max})`$ exists and is finite, and by
Theorem 18, $`\ell=0`$ if and only if every output law is a deterministic image of a
maximizing law.

Proof outline. Let $`g=H(K_{j_0})-h'_{\max}>0`$, where $`h'_{\max}`$ is the maximal entropy of
the subkernel on the other actions, and set $`\delta_x=g/4`$, $`\delta=g/8`$. A *pair* couples
$`p`$ i.i.d. samples of $`K_{j_0}`$ with an exact finite seed (from causal truncation) for
the subkernel on a window of length $`q`$, by the interval coupling whose tail atoms are
merged. Its entropy is at most
$`p\,H(K_{j_0})+\varepsilon(p,q)`$, where $`\varepsilon`$ collects the Hoeffding lower tail of the
product information, the split-atom term and the tail entropy $`T_q`$ of the subfamily
seed (bounded by the Chernoff upper tail of the Bellman envelope). With
$`D+2`$ pairs of sizes $`p_i=D+1-i`$ and windows $`q_i=p_{i-1}`$ arranged anti-diagonally, an
interleaved decoder reads action-$`j_0`$ outputs from the product samples and the other
outputs from the windows; every block is consumed before it is needed, so the decoder is
exact for adaptive policies at horizon $`n_D=\sum_i p_i`$. The middle excesses
$`\varepsilon(p,p+1)`$ are $`O(p\rho^p)`$ with $`\rho<1`$, hence summable, which bounds the
residual along $`n_D`$; monotonicity of the residual extends the bound to all $`n`$.

Lean:
- [`Kernel.residual_bdd`](CausalSeed/GapBound.lean#L374), with
  [`Kernel.UniqueMax`](CausalSeed/GapBound.lean#L161)
- [`Kernel.residual_limit`](CausalSeed/GapBound.lean#L428),
  [`Kernel.residual_limit_zero_iff`](CausalSeed/GapBound.lean#L435)
- Block absorption: [`Gap.heavy_mass_le`](CausalSeed/GapProduct.lean#L89) (Hoeffding lower
  tail of product information), [`Gap.tail_entropy_le`](CausalSeed/GapTail.lean#L102) (tail
  entropy $`T_q`$), [`Gap.piC_entropy_le'`](CausalSeed/GapPair.lean#L212) (pair coupling),
  [`Kernel.mkComp_entropy`](CausalSeed/GapComp.lean#L136)
- Interleaved decoder: [`Kernel.pathMass_split`](CausalSeed/GapDecoder.lean#L144),
  [`Kernel.decoder_exact`](CausalSeed/GapInterleave.lean#L324),
  [`Kernel.finiteCost_le_plan`](CausalSeed/GapInterleave.lean#L389)
- Block arithmetic and $`K`$: [`Gap.sep_family`](CausalSeed/GapBound.lean#L106),
  [`Kernel.costBits_family`](CausalSeed/GapBound.lean#L136),
  [`Kernel.summable_Fexc`](CausalSeed/GapBound.lean#L226)

### V. Structure of the causal constraint

**Theorem 20 (exact penalty).** Let $`G_{\ast}=\sup_T\bigl(C(T)-O(T)\bigr)`$, where $`O(T)`$
is the least entropy of an exact coupling that need not be causal. Then
$`\tfrac29\le G_{\ast}\le c_{\star}`$. For every $`\kappa\ge G_{\ast}`$,

```math
C(T)=\inf_\Gamma\bigl[H(\Gamma)+\kappa\,\Gamma(B)\bigr],
```

where $`B`$ is the set of incompatible joint transcripts. For $`\kappa>G_{\ast}`$, every
global minimizer is causal, and every $`\varepsilon`$-minimizer has
$`\Gamma(B)\le\varepsilon/(\kappa-G_{\ast})`$.

Lean:
- [`witness_gapSup_lower`](CausalSeed/Witness.lean#L1376)
- [`gapSup_le_shannonOverhead`](CausalSeed/Penalty.lean#L710)
- [`penaltyMin_eq_causalMin`](CausalSeed/Identity.lean#L569)
- [`global_minimizer_above_gap_is_causal`](CausalSeed/StrictPenalty.lean#L74)
- [`near_minimizer_badMass_le`](CausalSeed/StrictPenalty.lean#L18)

**Theorem 21 (arithmetic rigidity).** Let $`w`$ be a positive weight vector with total
mass one. Every exact policy-indexed decoder family on every finite tree is causally
realizable if and only if all subset sums of $`w`$ are distinct. With marginal error
$`\varepsilon\ge0`$, every $`\varepsilon`$-accurate family is realizable if and only if
$`2\varepsilon<\gamma`$, where
$`\gamma=\min_{A\ne B}\bigl|\sum_{i\in A}w_i-\sum_{i\in B}w_i\bigr|`$. Repair by
weight-preserving relabelings is characterized separately.

Lean:
- [`exact_rigidity`](CausalSeed/Profile.lean#L529)
- [`sharp_threshold`](CausalSeed/Profile.lean#L548)
- [`relabelRepair_iff_countStable`](CausalSeed/Relabel.lean#L1577)

### VI. Zero branches on infinite trees

Let $`T`$ be a locally finite history-dependent tree with nonnegative kernels
(`ZeroBranch.NNTree`): at each history finitely many actions, and for each action a finite
law $`K_{h,a}\ge0`$ that may vanish on some outputs. The reduced tree $`T^{+}`$
(`NNTree.plus`, an `ITree`) keeps at every history only the outputs of positive
probability, in their original order, without renormalizing. A history of $`T^{+}`$ lifts
injectively to a history of $`T`$ with the same probability. A causal decoder for $`T`$ on a
measure space $`(\Omega,\mu)`$ is a map to total response strategies of $`T`$ with
measurable coordinates. It is exact to horizon $`n`$ if every history of length at most
$`n`$ is reproduced with its path probability. $`T_n`$ is the depth-$`n`$ tree of $`T`$ with
all zero branches retained (`NNTree.Zt n`).

**Theorem 22 (zero branches preserve the seed space).** There are maps $`R`$ from total
strategies of $`T`$ to total strategies of $`T^{+}`$ and $`E`$ in the other direction with
$`R\circ E=\mathrm{id}`$ and $`E`$ injective, such that the following hold:

1. For every measure space and every $`n`$, an exact causal decoder for $`T`$ to horizon $`n`$
   exists if and only if one exists for $`T^{+}`$. The same holds with one decoder exact at
   every horizon. The seed space and its measure are unchanged; only the decoder is
   composed with $`R`$ or $`E`$.
2. A measure space carries an ordinary exact source for $`T`$ if and only if it carries one
   for $`T^{+}`$. The same holds for countable ordinary sources, with the same weights.
3. The spectrum is unchanged: $`F^{\ast}_{T_n}=F^{\ast}_{T^{+}_n}`$ and $`L(T_n)=L(T^{+}_n)`$
   for every $`n`$.

Lean (namespace `ZeroBranch.NNTree`):
- [`R_E`](CausalSeed/ZeroBranch.lean#L319), [`E_injective`](CausalSeed/ZeroBranch.lean#L326),
  [`pathMass_plus`](CausalSeed/ZeroBranch.lean#L246), [`lift_injective`](CausalSeed/ZeroBranch.lean#L185)
- [`seed_space_iff`](CausalSeed/ZeroBranchSeed.lean#L130),
  [`seed_space_iff_all`](CausalSeed/ZeroBranchSeed.lean#L135)
- [`ordinary_iff`](CausalSeed/ZeroBranchOrdinary.lean#L186),
  [`ordSrcC_iff`](CausalSeed/ZeroBranchOrdinary.lean#L292)
- [`F_Zt`](CausalSeed/ZeroBranchSpectrum.lean#L179), [`L_Zt`](CausalSeed/ZeroBranchSpectrum.lean#L183)

**Corollary 23 (Theorems 5–8 for kernels with zero entries).** Define, on $`T`$ itself,
$`C_n`$ and $`C_\infty`$ over countable seeds of total strategies of $`T`$,
$`L_\infty=\sup_nL(T_n)`$, $`F_\infty(t)=\inf_nF^{\ast}_{T_n}(t)`$ and $`q=\sup_tF_\infty(t)`$.
Then:

1. $`C_\infty=\sup_nC_n`$ (nats), and if this is finite one seed exact at every horizon
   attains it.
2. $`L_\infty\le C_\infty\le L_\infty+c_{\star}`$ (bits). An exact seed of finite entropy exists
   if and only if $`L_\infty<\infty`$, and then one attains $`C_\infty`$.
3. $`F_\infty(t)\to q`$ as $`t\to\infty`$, and $`q=\mathrm{atomQ}(T^{+})`$. Every exact causal
   decoder and every ordinary exact source of $`T`$ on a probability space with measurable
   singletons has atomic mass at most $`q`$. Some exact probability law on total strategies
   of $`T`$, and some ordinary exact source of $`T`$, have atomic mass exactly $`q`$. An exact
   countable seed exists if and only if $`q=1`$.
4. If $`T`$ has a countable ordinary exact source, one countable seed $`S`$ on $`T`$, exact at
   every horizon, satisfies
   $`R_\alpha(Z)\le O_\alpha(T)\le C_\alpha(T)\le H_\alpha(S)\le R_\alpha(Z)+d_\alpha`$ for every
   $`\alpha>0`$, and $`H_\infty(S)=C^{\mathrm R}_\infty(T)=O^{\mathrm R}_\infty(T)`$. Here $`Z`$ is
   the envelope limit variable of $`T^{+}`$, whose CDF on $`[0,\infty)`$ is $`F_\infty`$ of $`T`$.

Lean (namespace `ZeroBranch.NNTree`):
- [`infiniteCost_eq_iSup`](CausalSeed/ZeroBranchSeed.lean#L256),
  [`infiniteCost_attained`](CausalSeed/ZeroBranchSeed.lean#L262)
- [`envelope_sandwich`](CausalSeed/ZeroBranchTransfer.lean#L43),
  [`finite_seed_iff`](CausalSeed/ZeroBranchTransfer.lean#L50),
  [`infiniteCost_attained_sandwich`](CausalSeed/ZeroBranchTransfer.lean#L68)
- [`tendsto_Finf`](CausalSeed/ZeroBranchTransfer.lean#L85), [`q_eq`](CausalSeed/ZeroBranchTransfer.lean#L81),
  [`atomic_upper`](CausalSeed/ZeroBranchTransfer.lean#L144),
  [`atomic_attained`](CausalSeed/ZeroBranchTransfer.lean#L156),
  [`ordinary_atomic_le`](CausalSeed/ZeroBranchOrdinary.lean#L191),
  [`ordinary_atomic_attained`](CausalSeed/ZeroBranchOrdinary.lean#L197),
  [`countable_seed_iff_q_one`](CausalSeed/ZeroBranchTransfer.lean#L186)
- [`one_seed_all_orders_T`](CausalSeed/ZeroBranchOrdinary.lean#L306),
  [`OalphaT_eq`](CausalSeed/ZeroBranchOrdinary.lean#L295)

### VII. Random-walk maxima

Let $`m\ge1`$ and let $`Q`$ be a strictly positive law on a finite alphabet. The stationary
two-action kernel `Walk.TwoAction.kernel` has action $`U`$, uniform on $`m`$ symbols, and action
$`Q`$. Put $`h=\log_2 m`$, let $`Y_1,Y_2,\ldots`$ be i.i.d. with law $`Q`$, and set
$`X_j=-\log_2Q(Y_j)-h`$, $`S_k=X_1+\dots+X_k`$ and $`M_n=\max_{0\le k\le n}S_k`$. In Lean, the law
of $`(X_1,\dots,X_n)`$ is the finite product law on words of length $`n`$ (`Walk.Law.E`), so every
probability and expectation below is a finite weighted sum. $`C_n`$ is `Kernel.costBits n`.
The dyadic assumptions are $`m=2^{d}`$ for some $`d\in\mathbb N`$ and every atom of $`Q`$ a
power of $`1/2`$ (`TwoAction.Dyadic`).

**Theorem 24 (exact envelope identity).** For every $`n\ge0`$ and every real $`x`$,

```math
F^{\ast}_n(nh+x)=\Pr(M_n\le x),\qquad L_n=nh+\mathbb E M_n ,
```

and $`nh+\mathbb E M_n\le C_n\le nh+\mathbb E M_n+c_{\star}`$. Under the dyadic assumptions,
$`C_n=nh+\mathbb E M_n`$. No assumption on the sign of $`H(Q)-h`$ is needed.

Lean (namespace `Walk.TwoAction`):
- [`envelope_eq_cdfM`](CausalSeed/WalkEnvelope.lean#L107), [`envelopeMean_eq`](CausalSeed/WalkEnvelope.lean#L127)
- [`cost_sandwich`](CausalSeed/WalkEnvelope.lean#L150), [`cost_eq`](CausalSeed/WalkEnvelope.lean#L177)

**Theorem 25 (Spitzer's identity and the exact finite-horizon formula).** For every finite
increment law,

```math
\mathbb E M_n=\sum_{k=1}^n\frac{\mathbb E(S_k)_+}{k} .
```

Hence under the dyadic assumptions $`C_n=nh+\sum_{k=1}^n\mathbb E(S_k)_+/k`$, and in general this
expression is a lower bound on $`C_n`$ within $`c_{\star}`$. The proof is combinatorial: a cyclic
lemma shows that the $`n`$ rotations of any real word satisfy
$`\sum_i\bigl(\min_{1\le l\le n}S_l(\mathrm{rot}_i\,x)\bigr)_+=(S_n)_+`$, and
exchangeability gives $`\mathbb E M_n-\mathbb E M_{n-1}=\mathbb E(S_n)_+/n`$.

Lean:
- [`Walk.Law.spitzer`](CausalSeed/WalkMax.lean#L410), [`Walk.Law.EM_succ`](CausalSeed/WalkMax.lean#L396)
- [`Walk.cyclic_sum`](CausalSeed/WalkMax.lean#L172), [`Walk.sum_rot`](CausalSeed/WalkMax.lean#L222)
- [`Walk.TwoAction.cost_eq_spitzer`](CausalSeed/WalkEnvelope.lean#L182),
  [`Walk.TwoAction.cost_sandwich_spitzer`](CausalSeed/WalkEnvelope.lean#L156)

**Corollary 26 (negative drift).** Assume the dyadic assumptions and $`H(Q)<h`$, and let
$`\ell=\sum_{k\ge1}\mathbb E(S_k)_+/k`$. Then the series converges, $`C_n-nh`$ is nondecreasing,
and $`C_n-nh\to\ell=\sup_n(C_n-nh)`$. Some $`\theta>0`$ has
$`\lambda=\mathbb E e^{\theta X_1}<1`$, and for every such $`\theta`$ and every $`n`$,

```math
0\le\ell-(C_n-nh)\le\frac{\lambda^{n+1}}{\theta(n+1)(1-\lambda)} .
```

Here $`\ell`$ is characterized as the sum of the series and as the supremum of
$`\mathbb E M_n`$. The random variable $`M_\infty`$ is not constructed in Lean.

Lean:
- [`Walk.TwoAction.negative_drift`](CausalSeed/WalkLimit.lean#L182)
- [`Walk.Law.tail_bound`](CausalSeed/WalkLimit.lean#L38), [`Walk.Law.ESp_le_mgf`](CausalSeed/WalkLimit.lean#L89),
  [`Walk.Law.exists_theta`](CausalSeed/WalkLimit.lean#L125)

**Theorem 27 (reciprocal-gap family).** For an integer $`h\ge2`$, let $`U_h`$ be uniform on
$`2^h`$ symbols. Let $`Q_h`$ have $`2^{h-2}`$ atoms of mass $`2^{-(h-1)}`$, one atom of mass
$`2^{-h}`$ and $`2^h-2`$ atoms of mass $`2^{-(h+1)}`$. Write $`\Delta=2^{-h}`$, $`p=\tfrac12-\Delta`$
and $`q=\tfrac12`$. These are positive probabilities summing to one. The centered surprisals
are $`-1,0,1`$, $`H(U_h)-H(Q_h)=\Delta`$, and

```math
\lim_{n\to\infty}(C_n-nh)=\frac1{2\Delta}-1=2^{h-1}-1 .
```

With $`\theta=\tfrac12\ln(q/p)`$ and $`\lambda=\Delta+2\sqrt{pq}<1`$, for every $`n`$,

```math
0\le\frac1{2\Delta}-1-(C_n-nh)\le\frac{\lambda^{n+1}}{(e^\theta-1)(n+1)(1-\lambda)} .
```

The limit is identified without martingales: $`\Pr(M_n\ge j)\le r^j`$ with $`r=p/q`$, and
$`r^j-\Pr(M_n\ge j)\le r^{j/2}\lambda^n`$ for integers $`j\ge0`$. For $`h=2`$,
$`U_2=(\tfrac14,\tfrac14,\tfrac14,\tfrac14)`$ and $`Q_2=(\tfrac12,\tfrac14,\tfrac18,\tfrac18)`$ give
$`C_1-2=\tfrac14`$, $`C_2-4=\tfrac38`$ and $`C_n-2n\to1`$. The limits for $`h=2,3,4,8`$ are
$`1,3,7,127`$ bits.

Along the family every centered increment lies in $`\{-1,0,1\}`$, while
$`\Delta\cdot\lim_n(C_n-nh)\to\tfrac12`$ as $`h\to\infty`$. So no bound of the form
$`o(1/\Delta)`$ on the limiting excess holds uniformly over kernels with gap $`\Delta`$ and
increments in $`[-1,1]`$. The alphabets grow with $`h`$, and each fixed member has bounded
excess.

Lean (namespace `Walk.Family`; $`h=d+2`$, `A d` is the kernel):
- [`class_sum`](CausalSeed/WalkFamily.lean#L237) (masses), [`gap`](CausalSeed/WalkFamily.lean#L305),
  [`cost_limit`](CausalSeed/WalkFamily.lean#L360), [`limit_value`](CausalSeed/WalkFamily.lean#L366)
- [`sharper_bound`](CausalSeed/WalkFamily.lean#L419), [`mgf_θ`](CausalSeed/WalkFamily.lean#L402)
- [`example_h2`](CausalSeed/WalkFamily.lean#L461), [`limits_examples`](CausalSeed/WalkFamily.lean#L473),
  [`gap_times_limit`](CausalSeed/WalkFamily.lean#L480)
- [`Walk.Law.tl_le_rpow`](CausalSeed/WalkFamily.lean#L46), [`Walk.Law.tl_lower`](CausalSeed/WalkFamily.lean#L67),
  [`Walk.Law.EM_tendsto`](CausalSeed/WalkFamily.lean#L152)

## Verification

The development is the import closure of
[`CausalSeed/Main.lean`](CausalSeed/Main.lean). Pinned toolchain:

- Lean `4.35.0-rc3` ([`lean-toolchain`](lean-toolchain))
- Mathlib `7d6757bc18680044fc0ff6efc8ee20494b408556` ([`lakefile.toml`](lakefile.toml))

Build and audit:

```bash
lake build
lake env lean scripts/AxiomAudit.lean
```

[`scripts/AxiomAudit.lean`](scripts/AxiomAudit.lean) enumerates every theorem whose
defining module is `CausalSeed.*` and computes its axioms with `collectAxioms`.
Auto-generated declarations (equation lemmas, `sizeOf_spec`, injectivity lemmas,
instances) are excluded.

[`AXIOMS.txt`](AXIOMS.txt) records the result. All **2224** theorems in the 92 project
modules depend only on `propext`, `Classical.choice` and `Quot.sound`; seven depend on
no axiom. No theorem uses `sorryAx`, the build reports no `sorry` or `admit`, and the
project declares no `axiom`.

## Trusted definitions

The axiom audit certifies the proofs. It does not certify that the definitions mean
what the text says. Trust rests on the definitions below and on the statements of
the theorems above. Line numbers refer to the current revision.

| Lean name | Source | Meaning |
| --- | --- | --- |
| `Tree` | [Spectrum.lean#L20](CausalSeed/Spectrum.lean#L20) | finite controlled tree; actions `Fin nA`, outputs `Fin (nY a)`, kernel `K a y` with `Kpos : 0 < K a y`, `Ksum : ∑ y, K a y = 1` |
| `ITree`, `trunc` | [Atomic.lean#L513](CausalSeed/Atomic.lean#L513), [#L522](CausalSeed/Atomic.lean#L522) | locally finite infinite tree indexed by histories `List (ℕ × ℕ)` with positive kernels; depth-`n` truncation |
| `Kernel`, `Kernel.rounds` | [Spectrum.lean#L1296](CausalSeed/Spectrum.lean#L1296), [#L1307](CausalSeed/Spectrum.lean#L1307) | one positive kernel family repeated for `n` rounds |
| `Policy`, `Strategy`, `Leaf`, `leafMass` | [Spectrum.lean#L124](CausalSeed/Spectrum.lean#L124), [#L133](CausalSeed/Spectrum.lean#L133), [#L139](CausalSeed/Spectrum.lean#L139), [#L144](CausalSeed/Spectrum.lean#L144) | deterministic adaptive policy; total response strategy; transcript; its probability |
| `CompatiblePolicy`, `CompatibleStrategy`, `run` | [Spectrum.lean#L149](CausalSeed/Spectrum.lean#L149), [#L154](CausalSeed/Spectrum.lean#L154), [#L159](CausalSeed/Spectrum.lean#L159) | consistency of a transcript with a policy or strategy; the transcript of a strategy under a policy |
| `Atom`, `transcriptWeight`, `seedShannon`, `seedCDF` | [Spectrum.lean#L823](CausalSeed/Spectrum.lean#L823), [#L913](CausalSeed/Spectrum.lean#L913), [Entropy.lean#L648](CausalSeed/Entropy.lean#L648), [#L1393](CausalSeed/Entropy.lean#L1393) | finite seed as a weighted list of strategies; decoded transcript mass; entropy (bits); information CDF |
| `IStrategy`, `pathMass`, `policyRead` | [Capacity.lean#L557](CausalSeed/Capacity.lean#L557), [#L67](CausalSeed/Capacity.lean#L67), [AtomicCapacity.lean#L86](CausalSeed/AtomicCapacity.lean#L86) | strategy on the infinite tree; probability of a history; horizon-`n` transcript |
| `Completion.CountableSeed`, `.entropy`, `.ExactTo`, `.Exact` | [SeedRanking.lean#L20](CausalSeed/SeedRanking.lean#L20), [#L30](CausalSeed/SeedRanking.lean#L30), [#L36](CausalSeed/SeedRanking.lean#L36), [#L39](CausalSeed/SeedRanking.lean#L39) | countable law on infinite strategies; entropy (nats, in `[0,∞]`); every history of length `≤ n` (resp. every history) receives its path mass |
| `infoMass`, `policyCDF`, `Fstar` | [Entropy.lean#L53](CausalSeed/Entropy.lean#L53), [#L190](CausalSeed/Entropy.lean#L190), [#L226](CausalSeed/Entropy.lean#L226) | `-log₂ q`; information CDF of a policy; its pointwise minimum over policies |
| `envelopeMean`, `Completion.LInf`, `FInf` | [Entropy.lean#L651](CausalSeed/Entropy.lean#L651), [EnvelopeBridge.lean#L367](CausalSeed/EnvelopeBridge.lean#L367), [AtomicSpectrum.lean#L22](CausalSeed/AtomicSpectrum.lean#L22) | `L` (bits); `L_∞ = sup_n L_n`; `F_∞(t) = inf_n F*_n(t)` |
| `atomQ` | [Atomic.lean#L561](CausalSeed/Atomic.lean#L561) | `sup_K inf_{n,π}` of the mass of the `K` heaviest transcripts |
| `pmfEntropy`, `entTerm` | [Penalty.lean#L118](CausalSeed/Penalty.lean#L118), [#L52](CausalSeed/Penalty.lean#L52) | Shannon entropy (bits) of a finite law, with `entTerm 0 = 0` |
| `ordinaryMin`, `causalMin`, `gapSup` | [Penalty.lean#L626](CausalSeed/Penalty.lean#L626), [#L628](CausalSeed/Penalty.lean#L628), [#L696](CausalSeed/Penalty.lean#L696) | `O(T)`, `C(T)` over exact couplings (bits); `G_*` |
| `Completion.finiteCost`, `infiniteCost`, `Kernel.costBits` | [EntropyLimit.lean#L283](CausalSeed/EntropyLimit.lean#L283), [#L286](CausalSeed/EntropyLimit.lean#L286), [SqrtMain.lean#L99](CausalSeed/SqrtMain.lean#L99) | `C_n`, `C_∞` (nats); `C_n` in bits for a stationary kernel |
| `RenyiInf.shannonBits`, `H`, `Hinf` | [RenyiCountable.lean#L23](CausalSeed/RenyiCountable.lean#L23), [#L30](CausalSeed/RenyiCountable.lean#L30), [#L33](CausalSeed/RenyiCountable.lean#L33) | Shannon, Rényi and min-entropy of a countable law (bits, in `[0,∞]`) |
| `RenyiInf.OrdSource`, `Oα`, `Cα`, `Oinf`, `Cinf` | [RenyiSource.lean#L25](CausalSeed/RenyiSource.lean#L25), [RenyiInfinite.lean#L28](CausalSeed/RenyiInfinite.lean#L28), [#L31](CausalSeed/RenyiInfinite.lean#L31), [#L33](CausalSeed/RenyiInfinite.lean#L33), [#L35](CausalSeed/RenyiInfinite.lean#L35) | ordinary exact source; ordinary and causal Rényi optima |
| `RenyiInf.RZ`, `lawZ`, `RZmeas` | [RenyiInfinite.lean#L24](CausalSeed/RenyiInfinite.lean#L24), [RenyiLimitMeasure.lean#L117](CausalSeed/RenyiLimitMeasure.lean#L117), [#L324](CausalSeed/RenyiLimitMeasure.lean#L324) | `sup_n R_α(Z_n)`; the law of `Z` on `[0,∞] ⊂ EReal`; `R_α` of that law |
| `shannonOverhead`, `Renyi.dAlpha`, `RenyiInf.dA` | [Entropy.lean#L646](CausalSeed/Entropy.lean#L646), [RenyiFinite.lean#L180](CausalSeed/RenyiFinite.lean#L180), [RenyiCountable.lean#L36](CausalSeed/RenyiCountable.lean#L36) | `c⋆ = (1 + 1/ln 2)/2`; `d_α`; `d_α` with `d_1 = c⋆` |
| `Zero.ZTree` | [ZeroTree.lean#L255](CausalSeed/ZeroTree.lean#L255) | finite tree with nonnegative normalized kernels, all branches kept |
| `Zero.NNKernel`, `.red`, `.ztree`, `Zero.zcost`, `NNKernel.costBits` | [ZeroKernel.lean#L53](CausalSeed/ZeroKernel.lean#L53), [#L94](CausalSeed/ZeroKernel.lean#L94), [#L117](CausalSeed/ZeroKernel.lean#L117), [#L197](CausalSeed/ZeroKernel.lean#L197), [#L220](CausalSeed/ZeroKernel.lean#L220) | stationary kernel with nonnegative entries; its reduction to the support; the `n`-round tree with all branches; least exact Shannon entropy (bits) of a `ZTree`; `C_n` of the kernel |
| `Zero.tcost` | [ZeroCost.lean#L25](CausalSeed/ZeroCost.lean#L25) | least Shannon entropy (bits) of an exact finite law on response strategies of a positive tree |
| `OT.IsCoupling`, `OT.W1`, `OT.cdfDist` | [Wasserstein.lean#L21](CausalSeed/Wasserstein.lean#L21), [#L29](CausalSeed/Wasserstein.lean#L29), [#L32](CausalSeed/Wasserstein.lean#L32) | coupling of two laws on `ℝ`; `inf` over couplings of `E|X-Y|` in `[0,∞]`; `∫ |F_μ - F_ν|` |
| `Sqrt.IncFamily.limitLaw`, `CountableSeed.normLaw`, `seedLaw`, `envLaw` | [SqrtW1.lean#L70](CausalSeed/SqrtW1.lean#L70), [#L87](CausalSeed/SqrtW1.lean#L87), [GapW1.lean#L20](CausalSeed/GapW1.lean#L20), [#L75](CausalSeed/GapW1.lean#L75) | the law with CDF `F_{a,b}`; the law of `(J - c)/s`; the law of `J` for a finite seed; the law with CDF `F*` |
| `Sqrt.IncFamily.sA`, `sB`, `Flim` | [SqrtDefect.lean#L427](CausalSeed/SqrtDefect.lean#L427), [#L429](CausalSeed/SqrtDefect.lean#L429), [SqrtUniversality.lean#L26](CausalSeed/SqrtUniversality.lean#L26) | `a = max σ_a`, `b = min σ_a`; the limit profile `F_{a,b}` (half-normal if `b = 0`) |
| `Sqrt.IncFamily.sig2`, `m3`, `law`, `eG` | [SqrtDefect.lean#L424](CausalSeed/SqrtDefect.lean#L424), [MomentFourier.lean#L369](CausalSeed/MomentFourier.lean#L369), [#L116](CausalSeed/MomentFourier.lean#L116), [MomentLower.lean#L21](CausalSeed/MomentLower.lean#L21) | variance and third moment of the centered information of an action; the law `μ_n` with CDF `G_n`; its mean `∫ (G_0 - G)` |
| `Sqrt.IncFamily.mom`, `measOf`, `Nondeg` | [MomentTaylor.lean#L116](CausalSeed/MomentTaylor.lean#L116), [MomentWidth.lean#L79](CausalSeed/MomentWidth.lean#L79), [MomentAssembly.lean#L176](CausalSeed/MomentAssembly.lean#L176) | `E X_j^i`; the law of one increment as a finitely supported measure; the symmetric-pair hypothesis of Theorem 16 |
| `Kernel.EqualEntropy`, `actEntropy`, `hmax`, `floorConst` | [SqrtBridge.lean#L19](CausalSeed/SqrtBridge.lean#L19), [CausalFloor.lean#L145](CausalSeed/CausalFloor.lean#L145), [#L150](CausalSeed/CausalFloor.lean#L150), [#L181](CausalSeed/CausalFloor.lean#L181) | common entropy `h`; `H(K_a)`; `h_max`; the Gaussian integral `K` |
| `Dyadic.wt`, `massL`, `cdfL` | [DyadicCouple.lean#L18](CausalSeed/DyadicCouple.lean#L18), [#L28](CausalSeed/DyadicCouple.lean#L28), [#L31](CausalSeed/DyadicCouple.lean#L31) | `2^{-k}`; a dyadic law as a list of (level, payload); its expectation functional and information CDF |
| `Dyadic.DyadicTree`, `Kernel.IsDyadic` | [DyadicTree.lean#L17](CausalSeed/DyadicTree.lean#L17), [DyadicKernel.lean#L132](CausalSeed/DyadicKernel.lean#L132) | every kernel entry is `(1/2)^c` with `c : ℕ` |

## Repository layout

All modules are in [`CausalSeed/`](CausalSeed); `Main.lean` imports them all.

**Finite trees**
- `Spectrum`: trees, policies, strategies, transcripts, the greedy trace, stationary kernels.
- `Entropy`: the information CDF, the envelope, the Shannon sandwich, causal realization.
- `Gap`: the CDF-gap identity and finite-tree consequences.
- `Note`: constants and finite numerical facts ($`c_{\star}`$, $`\theta_\alpha`$, $`\log_2(8/5)`$).
- `SecondOrder`: Gaussian integrals for the profile mean.
- `Probe`: policy extensions used by the lower bounds.

**Couplings, penalty and rigidity**
- `Penalty`: couplings, ordinary and causal optima, $`G_{\ast}`$, the penalized problem.
- `Close`, `Transport`, `Identity`: residual flows, leaf transport, the exact-penalty identity.
- `StrictPenalty`: strict compatibility above $`G_{\ast}`$ and its stability.
- `Witness`: the witness tree for $`G_{\ast}\ge 2/9`$.
- `Arithmetic`, `Profile`: subset-sum gaps and arithmetic rigidity.
- `Relabel`: repair by relabeling.

**Infinite horizons**
- `Atomic`, `Capacity`, `MeasureCompletion`, `AtomicCapacity`: infinite trees, path mass, limiting strategies, atomic capacity.
- `AtomicSpectrum`: $`\mathrm{atomQ}=\lim F_\infty`$.
- `EntropyLimit`, `SeedRanking`, `EnvelopeBridge`: countable seeds, ranking, the projective identity, the infinite sandwich.
- `SeedDataProcessing`, `FiniteSeedExtension`, `AlphabetSeed`, `InfiniteEnvelope`: arbitrary countable alphabets and the bit-valued infinite envelope.

**Zero-probability branches**
- `ZeroGame`, `ZeroTree`, `ZeroClosure`: an abstract finite game, trees with nonnegative kernels, the closure theorem.
- `ZeroKernel`, `ZeroCost`: stationary kernels with zero entries, their reduction, and the equality of costs.
- `ZeroBranch`, `ZeroBranchSeed`: infinite trees with nonnegative kernels, the reduced tree, the maps $`R`$ and $`E`$, preservation of the seed space and transfer of the costs (Theorem 22, Corollary 23).
- `ZeroBranchSpectrum`, `ZeroBranchLeaves`: equality of the finite-horizon envelopes, and the policy and transcript maps between $`T_n`$ and $`T^{+}_n`$.
- `ZeroBranchTransfer`, `ZeroBranchOrdinary`: the envelope sandwich, atomic capacity and Rényi seed on $`T`$, and ordinary sources.

**Rényi spectrum**
- `RenyiFinite`: the finite-horizon Rényi sandwich.
- `RenyiCountable`: Rényi entropy of countable laws.
- `RenyiSource`: ordinary exact sources.
- `RenyiLimit`: the diagonal limit seed.
- `RenyiInfinite`: the infinite-horizon theorem.
- `RenyiLimitLaw`, `RenyiLimitMeasure`: the law of $`Z`$ and its moments.

**Stationary kernels**
- `Bellman`, `BellmanCompare`: the Bellman operator and barrier propagation.
- `SqrtProfile`, `SqrtDefect`, `SqrtCompare`: the profile $`F_{a,b}`$, the one-step defect, the CDF comparison.
- `SqrtTails`, `SqrtMean`, `SqrtRate`, `SqrtBridge`, `SqrtMain`, `SqrtPerturb`, `SqrtGeneral`: Hoeffding tails, the mean identity, the rate, the $`b=0`$ perturbation, the main theorem.
- `SqrtNumerics`: integer inequalities.
- `SqrtUniversality`, `SqrtUniversalityCountable`: $`W_1`$ universality in CDF form.
- `Wasserstein`, `SqrtW1`, `GapW1`: $`W_1`$ by optimal transport, the quantile coupling, universality and the gap identity for it.
- `MomentClass`: the $`\Theta(\sqrt n)`$ branch of the moment classification.
- `MomentFourier`, `MomentLower`: the Fourier lower bound for $`\int|E_jG_n-E_kG_n|`$ and the $`\Omega(\log n)`$ lower bound.
- `GapImage`: one-step superadditivity, the monotone residual, and deterministic images.
- `GapZero`: the zero set of the residual (Theorem 18).
- `GapCoupling`: the interval coupling of two finite laws and its entropy bound (the finite core of block absorption).
- `GapProduct`, `GapTail`, `GapPair`, `GapComp`: product samples and their Hoeffding tail, the subfamily tail entropy, the pair coupling and its entropy.
- `GapDecoder`, `GapBlocks`, `GapInterleave`: the subkernel, history splitting, block utilities, and exactness of the interleaved decoder.
- `GapBound`: the anti-diagonal block family, the constant $`K`$, and Theorem 19.
- `MomentTaylor`, `MomentDecay`, `MomentSmooth`, `MomentWidth`, `MomentUpper`, `MomentAssembly`: the Taylor bound, total-variation decay, uniform splines, the width recursion, and the $`O(\log n)`$, $`O(1)`$ and $`\Theta(\log n)`$ theorems.
- `CausalFloor`: the causal Shannon floor.
- `Subadditive`: concatenation of seeds, $`C_{m+n}\le C_m+C_n`$, and the Fekete limit.
- `DyadicCouple`, `DyadicTree`, `DyadicKernel`: dyadic exactness.

**Random-walk maxima**
- `WalkMax`: finite i.i.d. words, exchangeability, the cyclic lemma and Spitzer's identity.
- `WalkEnvelope`: the two-action kernel, the exact envelope identity, and the exact cost (Theorems 24 and 25).
- `WalkLimit`: the tail bound, the exponential-moment bounds, and the negative-drift corollary (Corollary 26).
- `WalkFamily`: tails of maxima for increments in $`\{-1,0,1\}`$, and the reciprocal-gap family (Theorem 27).

**Mathematical expositions** (LaTeX/PDF at the repository root)
- `bellman_square_root`: the square-root asymptotic.
- `universal_causal_seed`: the Rényi spectrum.
- `atomic_capacity`: atomic capacity.
- `completion_proof`: infinite seeds and entropy attainment.
- `arithmetic_causality`: arithmetic rigidity.
- `causal_spectrum.pdf`, `one_seed_entropy.pdf`.

## Scope and open problems

**Scope.**
- All local alphabets are finite and nonempty.
- Policies are deterministic and adaptive.
- Theorems 3, 14, 22 and Corollary 23 and the nonnegative-kernel parts of Theorems 15 and 16
  allow zero kernel entries; all other results assume strictly positive kernels.

**Open mathematical problems.**
- The exact value of $`G_{\ast}\in[\tfrac29,c_{\star}]`$, and whether all minimizers are causal
  at $`\kappa=G_{\ast}`$.
- The second-order term of $`C_n-nh`$ when $`a=b`$, where the $`\sqrt n`$ coefficient
  vanishes.
- Optimality of the constants $`c_{\star}`$ and $`d_\alpha`$.

**Hypotheses of Theorem 16.** Parts 1 and 2 require a reference action whose law has two
distinct values and whose variance (and, for part 2, third moment) every action shares.
The excluded case, in which every action is a point mass, is not covered by the formal
statement.

## Attribution

The additive constant and the nonlinear diffusion profile have antecedents in the
literature. This repository does not claim originality or priority. Its purpose is to
state the causal simulation results precisely and to provide formal proofs.
Comparison with prior work is a separate task.
