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
  universality, and the linear growth rate when the actions' entropies differ. With
  unequal entropies, the $`\sqrt n`$ term is determined by the maximizing actions alone.
- With equal entropies and variances, $`C_n=nh+\frac{\kappa_+-\kappa_-}{3v\sqrt{2\pi e}}\ln n+O(1)`$.
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

### VIII. Maximal-entropy reduction

Let $`\kappa`$ be a stationary positive kernel, write $`I_a=-\log_2K_a(Y)`$ for
$`Y\sim K_a`$, and let $`F_n`$, $`L_n`$, $`C_n`$ be the envelope (`Fstar (κ.rounds n)`), its
mean and the optimal cost at horizon $`n`$, in bits. For a nonempty set $`S`$ of actions,
$`\kappa_S`$ (`κ.sub S hS`) is the kernel of the actions in $`S`$, with envelope $`F^{\ast}_n`$,
mean $`L^{\ast}_n`$ and cost $`C^{\ast}_n`$. An action $`i_0\in S`$ *dominates at rate*
$`\theta>0`$ (`Dominates S i₀ θ`) if

```math
\mathbb E\,e^{\theta I_j}\;\mathbb E\,e^{-\theta I_{i_0}}\le1\qquad\text{for every }j\notin S .
```

Theorems 11, 13 and 19 already treat unequal entropies: they give the rate
$`h_{\max}`$, the bound $`C_n\ge nh_{\max}`$, and a bounded residual when exactly one action
attains $`h_{\max}`$. The results below cover any number of maximizing actions: the
second-order behaviour of $`C_n`$ is that of the maximizing subfamily alone, whatever the
variances of the other actions.

**Theorem 28 (exponential comparison).** If $`i_0\in S`$ dominates at rate $`\theta`$, then
for every $`n`$, every real $`x`$ and every $`r\ge0`$,

```math
F^{\ast}_n(x-r)-e^{-\theta r}\le F_n(x)\le F^{\ast}_n(x).
```

Domination holds whenever $`I_a\le M`$ for all actions and outputs, every $`j\notin S`$ has
$`H(K_j)+\Delta\le H(K_{i_0})`$, and $`0<\theta\le4\Delta/M^2`$ (Hoeffding's lemma applied to
each factor). The proof is a finite induction on the Bellman recursion: for a dominated
action the bound is applied pointwise on the product of the two output laws, with the
shift $`r+I_{i_0}-I_j`$.

Lean:
- [`Kernel.Fstar_compare`](CausalSeed/MaxEntropy.lean#L162), with
  [`Kernel.Dominates`](CausalSeed/MaxEntropy.lean#L60) and [`Kernel.sub`](CausalSeed/MaxEntropy.lean#L27)
- [`Kernel.sub_shift_le`](CausalSeed/MaxEntropy.lean#L68), [`Kernel.G_le_sub`](CausalSeed/MaxEntropy.lean#L51)
- [`Kernel.dominates_of_gap`](CausalSeed/MaxEntropy.lean#L186),
  [`MaxEntropy.finite_hoeffding`](CausalSeed/MaxEntropyHoeffding.lean#L13)

**Theorem 29 (mean and cost comparison).** Restricting a seed of $`\kappa`$ to the actions of
$`S`$ keeps it exact, so $`C^{\ast}_n\le C_n`$ for every $`S`$. If moreover $`i_0\in S`$
dominates at rate $`\theta`$ and $`0\le I_a\le M`$, then with
$`B_n=\bigl(1+\ln(1+\theta nM)\bigr)/\theta`$,

```math
0\le L_n-L^{\ast}_n\le B_n,\qquad 0\le C_n-C^{\ast}_n\le B_n+c_{\star}.
```

Here $`L_n-L^{\ast}_n=\int_0^{nM}(F^{\ast}_n-F_n)`$, which is bounded by
$`r+nMe^{-\theta r}`$ for every $`r\ge0`$ and optimized at $`r=\ln(1+\theta nM)/\theta`$.

Lean:
- [`Kernel.envelopeMean_compare`](CausalSeed/MaxEntropy.lean#L263)
- [`Kernel.costBits_compare`](CausalSeed/MaxEntropy.lean#L396)
- [`Kernel.costBits_sub_le`](CausalSeed/MaxEntropy.lean#L384),
  [`Kernel.restrictSeed_exactTo`](CausalSeed/MaxEntropy.lean#L375)

**Theorem 30 (maximal-entropy reduction).** In the setting of Theorem 29, suppose all
actions of $`S`$ have the same entropy $`h`$ (for instance, $`S`$ is the set of maximizing
actions), and let $`a_{\ast}`$, $`b_{\ast}`$ be the largest and smallest standard deviation of
$`I_i`$ over $`i\in S`$. Then

```math
C_n=nh+\sqrt{\tfrac{2}{\pi}}\,(a_{\ast}-b_{\ast})\sqrt n+o(\sqrt n),
```

and the same holds for $`L_n`$ and for the entropy of any seeds $`S_n`$ with
$`L_n\le H(S_n)\le L_n+c_{\star}`$. If $`b_{\ast}>0`$, the remainder in the expansion of
$`C_n`$ is at most $`K\,n^{1/4}\log n`$ for all $`n\ge3`$.

Lean:
- [`Kernel.cost_tendsto_maxEntropy`](CausalSeed/MaxEntropyReduction.lean#L68)
- [`Kernel.envelope_tendsto_maxEntropy`](CausalSeed/MaxEntropyReduction.lean#L80)
- [`Kernel.greedy_tendsto_maxEntropy`](CausalSeed/MaxEntropyReduction.lean#L96)
- [`Kernel.cost_rate_maxEntropy`](CausalSeed/MaxEntropyReduction.lean#L117)

**Corollary 31 (no intermediate power-law regime).** In the setting of Theorem 30:
1. If $`a_{\ast}>b_{\ast}`$, there are $`c,C>0`$ with $`c\sqrt n\le C_n-nh\le C\sqrt n`$ for all
   large $`n`$.
2. If all actions of $`S`$ have the same surprisal variance and one of them satisfies the
   symmetric-pair hypothesis of Theorem 16 (every law with two distinct values does), then
   $`C_n-nh\le C(1+\log n)`$ for all $`n\ge1`$.
3. If all actions of $`S`$ have the same surprisal variance and two of them have different
   third centered moments, then $`c\log n\le C_n-nh\le C\log n`$ for all large $`n`$.

Lean:
- [`Kernel.excess_sqrt_order`](CausalSeed/MaxEntropyReduction.lean#L155)
- [`Kernel.excess_log_upper_maxEntropy`](CausalSeed/MaxEntropyReduction.lean#L174)
- [`Kernel.excess_log_theta_maxEntropy`](CausalSeed/MaxEntropyReduction.lean#L199)

**Proposition 32 (a separating example).** Let

```math
P=(\tfrac14,\tfrac14,\tfrac14,\tfrac14),\quad Q=(\tfrac12,\tfrac18,\tfrac18,\tfrac18,\tfrac18),\quad
R=(\tfrac12,\tfrac14,\tfrac18,\tfrac1{16},\tfrac1{16}).
```

Then $`H(P)=H(Q)=2`$, $`H(R)=\tfrac{15}8`$, and the surprisal variances are $`0`$, $`1`$ and
$`\tfrac{71}{64}`$. With $`S=\{P,Q\}`$, $`\theta=\ln\tfrac65`$ and $`M=4`$,

```math
\mathbb E\,e^{\theta I_R}\;\mathbb E\,e^{-\theta I_P}=\tfrac{299}{300},
```

so $`0\le C_n-C^{\ast}_n\le\bigl(1+\ln(1+4\theta n)\bigr)/\theta+c_{\star}`$ and

```math
\frac{C_n-2n}{\sqrt n}\longrightarrow\sqrt{\tfrac{2}{\pi}} .
```

The action with the largest variance does not enter the $`\sqrt n`$ term.

Lean (namespace `Kernel.PQR`):
- [`H_P`](CausalSeed/MaxEntropyExample.lean#L59), [`H_Q`](CausalSeed/MaxEntropyExample.lean#L62),
  [`H_R`](CausalSeed/MaxEntropyExample.lean#L65), [`var_P`](CausalSeed/MaxEntropyExample.lean#L70),
  [`var_Q`](CausalSeed/MaxEntropyExample.lean#L73), [`var_R`](CausalSeed/MaxEntropyExample.lean#L76)
- [`certificate`](CausalSeed/MaxEntropyExample.lean#L98), [`dominates`](CausalSeed/MaxEntropyExample.lean#L104)
- [`cost_compare`](CausalSeed/MaxEntropyExample.lean#L160), [`cost_tendsto`](CausalSeed/MaxEntropyExample.lean#L152)

### IX. Toward the sharp logarithmic coefficient

Let $`X_1,\dots,X_d`$ be centered, finitely supported increments with common variance
$`v>0`$ and third moments $`\kappa_i`$, and let $`\kappa_\pm`$ be the largest and smallest of
them. Write $`A_if(x)=\mathbb E f(x-X_i)`$, $`Tf=\min_iA_if`$, $`Uf=\max_iA_if`$, and
$`G_n=T^nH`$, $`V_n=U^nH`$ for the lower and upper policy envelopes. Put
$`e_n=\int(H-G_n)`$ (`eG (G n)`) and $`w_n=\int(V_n-G_n)`$ (`Wint n`). For a stationary
kernel with common entropy $`h`$, $`e_n=L_n-nh`$.

**Theorem 33 (envelope width).** There is a constant $`C`$ with

```math
e_n\le C(1+\log n),\qquad w_n\le C(1+\log n)\qquad\text{for all }n .
```

No further hypothesis is needed: a centered law of positive variance has two distinct atoms,
so the symmetric-pair hypothesis of Theorem 16 holds automatically. The width is bounded
directly, by the same recursion that bounds $`e_n`$ in Theorem 16.

Lean:
- [`Sqrt.IncFamily.width_log_upper`](CausalSeed/LogWidth.lean#L119)
- [`Sqrt.IncFamily.Wint_log_upper`](CausalSeed/LogWidth.lean#L67),
  [`Sqrt.IncFamily.nondeg_of_sig2_pos`](CausalSeed/LogWidth.lean#L22)

**Theorem 34 (integrated amplification and propagation).**
1. For $`R\in C^1`$ with $`R'`$ continuous and integrable and $`R\to0`$ at $`-\infty`$,
   ```math
   \int U^n|R|\le\|R\|_1+\|R'\|_1\,w_n .
   ```
2. For all functions $`f,g`$, $`|T^nf-T^ng|\le U^n|f-g|`$ pointwise.
3. For every sequence of functions $`u_0,u_1,\dots`$, with $`R_j=u_{j+1}-Tu_j`$,
   ```math
   |T^nu_0-u_n|\le\sum_{j<n}U^{\,n-1-j}|R_j|\qquad\text{pointwise.}
   ```

Together with Theorem 33, these reduce an $`L^1`$ comparison of $`G_n`$ with any smooth
profile to $`L^1`$ bounds on the one-step residuals and their derivatives.

Lean:
- [`Sqrt.IncFamily.amp_lintegral`](CausalSeed/LogWidth.lean#L138)
- [`Sqrt.IncFamily.abs_Tit_sub_le`](CausalSeed/LogWidth.lean#L238),
  [`Sqrt.IncFamily.abs_T_sub_le`](CausalSeed/LogWidth.lean#L217), with
  [`Sqrt.IncFamily.Tit_H`](CausalSeed/LogWidth.lean#L182) ($`T^nH=G_n`$)
- [`Sqrt.IncFamily.propagation`](CausalSeed/LogWidth.lean#L245)

**Analytic result (formalized for the CDF envelopes, Theorem 40).** The manuscript
[`sharp_logarithmic_coefficient`](sharp_logarithmic_coefficient.pdf) derives

```math
e_n=\frac{\kappa_+-\kappa_-}{3v\sqrt{2\pi e}}\,\ln n+O\bigl(\sqrt{\ln n\,\ln\ln n}\bigr),
```

and the same expansion for $`C_n-nh`$ in bits. It combines Theorems 33 and 34 with an explicit
corrector $`u_t=\Phi(z)+t^{-1/2}B(z)`$, $`z=(x-c\ln t)/\sqrt{vt}`$, where $`B`$ solves
$`B''+zB'+B=2(a\phi-f)`$, and with $`L^1`$ Taylor bounds for the residuals of that profile.
Amplification in majorant form (Theorem 36), the Gaussian norms (Theorem 37), the corrector
(Theorem 38), the residual lemma (Theorem 39) and the propagation with the choice of $`t_0`$
(Theorem 40) are formal. Theorem 40 gives both the $`W_1`$ statement, in its CDF form, and the
mean statement for $`e_n`$, and Theorem 41 transfers the expansion to $`C_n`$ and $`L_n`$.

**Proposition 35 (a dyadic pair).** Let $`P=(\tfrac14,\tfrac1{16}^{\times12})`$ and
$`Q=(\tfrac18^{\times6},\tfrac1{32}^{\times8})`$. Both have entropy $`\tfrac72`$ bits and
information variance $`\tfrac34`$, and their centered third moments are $`-\tfrac34`$ and
$`\tfrac34`$. Hence there are $`0<c\le C`$ with

```math
c\log n\le C_n-\tfrac72n\le C\log n
```

for all large $`n`$ (and the same for $`L_n`$), and Theorem 33 applies. Theorem 41 sharpens this to
$`C_n=\tfrac72n+\tfrac{2}{3\sqrt{2\pi e}}\ln n+O(\sqrt{\ln n\ln\ln n})`$. Theorem 46 improves the
remainder to $`O(1)`$. The predicted
coefficient $`(\kappa_+-\kappa_-)/(3v\sqrt{2\pi e})=2/(3\sqrt{2\pi e})`$ lies in
$`(0.1613,\,0.1614)`$. A floating-point Bellman computation on the half-bit lattice gives
$`e_n-0.161314\ln n=0.6254`$ to four decimals for $`n=10^3,\dots,3\cdot10^5`$; this numerical
evidence is not part of the formal development.

Lean (namespace `Kernel.LogPair`):
- [`equalEntropy`](CausalSeed/LogExample.lean#L46), [`sig2_eq`](CausalSeed/LogExample.lean#L55),
  [`m3_P`](CausalSeed/LogExample.lean#L62), [`m3_Q`](CausalSeed/LogExample.lean#L68)
- [`excess_log_theta`](CausalSeed/LogExample.lean#L76), [`width_log_upper`](CausalSeed/LogExample.lean#L86)
- [`coeff_bounds`](CausalSeed/LogExample.lean#L99)

**Theorem 36 (amplification under a majorant).** Call $`S`$ a $`C^1`$ majorant if $`S\ge0`$,
$`S'`$ is continuous and integrable, and $`S(x)\to0`$ as $`x\to-\infty`$. Then:

1. if $`|R|\le S`$ pointwise, $`\int U^n|R|\le\|S\|_1+\|S'\|_1\,w_n`$, with no regularity
   required of $`R`$;
2. if $`|f-g|\le S`$, then $`\|T^nf-T^ng\|_1\le\|S\|_1+\|S'\|_1\,w_n`$;
3. if every residual satisfies $`|u_{j+1}-Tu_j|\le S_j`$ with $`C^1`$ majorants $`S_j`$, then

   ```math
   \|T^nu_0-u_n\|_1\le\sum_{j<n}\bigl(\|S_j\|_1+\|S_j'\|_1\,w_{n-1-j}\bigr).
   ```

This removes the need for a $`W^{1,1}`$ or BV extension of Theorem 34: the residuals of the
corrector (which involve a minimum over actions) and the initial comparison (which involves
the step $`H`$) only have to be dominated by smooth majorants.

Lean:
- [`Sqrt.IncFamily.Majorant`](CausalSeed/LogAmp.lean#L27), [`Sqrt.IncFamily.U_nonneg`](CausalSeed/LogAmp.lean#L19)
- [`Sqrt.IncFamily.amp_majorant`](CausalSeed/LogAmp.lean#L39)
- [`Sqrt.IncFamily.stability_lintegral`](CausalSeed/LogAmp.lean#L50)
- [`Sqrt.IncFamily.propagation_lintegral`](CausalSeed/LogAmp.lean#L60)

**Theorem 37 (Gaussian derivative norms).** Let $`\phi(z)=e^{-z^2/2}/\sqrt{2\pi}`$. Then
$`\phi'=-z\phi`$, $`\phi''=(z^2-1)\phi`$, all three are integrable, and

```math
\int\phi=1,\qquad\int\phi'=\int\phi''=0,\qquad\int|\phi'|=2\phi(0),\qquad\int|\phi''|=4\phi(1).
```

For every profile $`g`$ and $`s>0`$, $`\int|g((x-m)/s)|\,dx=s\int|g|`$. In particular the first
three $`x`$-derivatives of $`\Phi((x-m)/s)`$ have $`L^1`$ norms $`1`$, $`2\phi(0)/s`$ and
$`4\phi(1)/s^2`$.

Lean:
- [`LogGauss.hasDerivAt_phi`](CausalSeed/LogGauss.lean#L27), [`LogGauss.hasDerivAt_dphi`](CausalSeed/LogGauss.lean#L34),
  [`LogGauss.integrable_ddphi`](CausalSeed/LogGauss.lean#L59)
- [`LogGauss.integral_phi`](CausalSeed/LogGauss.lean#L80), [`LogGauss.integral_ddphi`](CausalSeed/LogGauss.lean#L90),
  [`LogGauss.integral_abs_dphi`](CausalSeed/LogGauss.lean#L95), [`LogGauss.integral_abs_ddphi`](CausalSeed/LogGauss.lean#L115)
- [`LogGauss.integral_abs_comp_affine`](CausalSeed/LogGauss.lean#L141), [`LogGauss.gauss_scaled_norms`](CausalSeed/LogGauss.lean#L157)

**Theorem 38 (the resonant corrector).** Let $`\beta\le\alpha`$ be real; in the application
$`\alpha=\kappa_+/(6v^{3/2})`$ and $`\beta=\kappa_-/(6v^{3/2})`$. Put

```math
f(z)=\min\bigl(-\alpha\phi''(z),-\beta\phi''(z)\bigr),\quad a=\int f,\quad g=2(a\phi-f),\quad
J(z)=\int_{-\infty}^zg,\quad B(z)=\phi(z)\int_0^z\frac{J}{\phi}.
```

Then:

1. $`f=-\alpha\phi''+(\alpha-\beta)\mathbf 1_{[-1,1]}\phi''`$ and $`a=-2(\alpha-\beta)\phi(1)`$, so $`\int g=0`$;
2. $`B\in C^2`$, with $`B'=J-zB`$ and $`B''=g-B-zB'`$; in particular
   $`B''+zB'+B=2(a\phi-f)`$;
3. $`|J|\le K(1+|z|)^2\phi`$, $`|B|\le K(1+|z|)^3\phi`$, $`|B'|\le K(1+|z|)^4\phi`$ and
   $`|B''|\le K(1+|z|)^5\phi`$ for a finite $`K`$; hence $`B,B',B''`$ are integrable.

The tail bounds use the primitive $`-(y^2+2)\phi(y)`$ of $`y^3\phi(y)`$ instead of Mills'
ratio. The local Lipschitz bound for $`B''`$ (the weak $`B'''`$) is part of the residual
lemma.

Lean:
- [`LogGauss.cf_eq`](CausalSeed/LogCorrector.lean#L97), [`LogGauss.ca_eq`](CausalSeed/LogCorrector.lean#L112), [`LogGauss.integral_cg`](CausalSeed/LogCorrector.lean#L131)
- [`LogGauss.hasDerivAt_cJ`](CausalSeed/LogCorrector.lean#L159), [`LogGauss.hasDerivAt_cB`](CausalSeed/LogCorrector.lean#L287),
  [`LogGauss.hasDerivAt_cdB`](CausalSeed/LogCorrector.lean#L293), [`LogGauss.cB_first_order`](CausalSeed/LogCorrector.lean#L299), [`LogGauss.cB_ode`](CausalSeed/LogCorrector.lean#L303)
- [`LogGauss.abs_cJ_le`](CausalSeed/LogCorrector.lean#L205), [`LogGauss.abs_cB_le`](CausalSeed/LogCorrector.lean#L325), [`LogGauss.abs_cdB_le`](CausalSeed/LogCorrector.lean#L351),
  [`LogGauss.abs_cddB_le`](CausalSeed/LogCorrector.lean#L370), [`LogGauss.integrable_cddB`](CausalSeed/LogCorrector.lean#L403)

**Theorem 39 (the residual lemma in majorant form).** Let the increment family be centered
with common variance $`v>0`$, let $`\kappa_\pm`$ be the largest and smallest third moments, and
put $`\alpha=\kappa_+/(6v^{3/2})`$, $`\beta=\kappa_-/(6v^{3/2})`$, $`c=-\sqrt v\,a`$. Then:

1. $`c=(\kappa_+-\kappa_-)/(3v\sqrt{2\pi e})`$, and $`\min_j\bigl[-\tfrac{\kappa_j}{6v^{3/2}}\phi''(z)\bigr]=f(z)`$;
2. $`|B''(w)-B''(z)|\le L\,E(z)\,|w-z|`$ for $`|w-z|\le D`$, where $`E(z)=(1+z^2)^4e^{-z^2/8}`$;
3. with $`z=(x-c\ln t)/\sqrt{vt}`$ and $`u_t(x)=\Phi(z)+t^{-1/2}B(z)`$, there is $`K`$ such that for all
   $`t\ge1`$ and $`x`$

   ```math
   \bigl|u_{t+1}(x)-(Tu_t)(x)\bigr|\le K\,t^{-2}E(z).
   ```

   The right side $`S_t`$ is a $`C^1`$ majorant with $`\|S_t\|_1=K_1t^{-3/2}`$ and
   $`\|S_t'\|_1=K_2t^{-2}`$.

The proof uses Taylor remainders in $`z`$ for the spatial translations, a time Taylor
expansion with an explicit second derivative, and the profile identity
$`\partial_tu-\tfrac v2\partial_x^2u=t^{-3/2}f(z)-(c/\sqrt v)\,t^{-2}B'(z)`$. Gaussian windows
$`(1+|w|)^k\phi(w)\le C_DE(z)`$ for $`|w-\lambda z|\le D`$ with $`\lambda^2\ge\frac12`$ handle every remainder.
This is the manuscript's estimate $`\|R_t\|_1+\|R_t'\|_1\le Kt^{-3/2}`$ in the form Theorem 36
consumes: a pointwise bound by a smooth majorant replaces the weak derivative of $`R_t`$.

Lean:
- [`LogGauss.cdrift_eq`](CausalSeed/LogResidual.lean#L267), [`LogGauss.inf'_eq_cf`](CausalSeed/LogResidual.lean#L241), [`LogGauss.ca_eq_neg_cdrift`](CausalSeed/LogResidual.lean#L262)
- [`LogGauss.cddB_lip`](CausalSeed/LogResidual.lean#L93), [`LogGauss.taylor_Phi`](CausalSeed/LogResidual.lean#L155), [`LogGauss.taylor_cB`](CausalSeed/LogResidual.lean#L191)
- [`LogGauss.window`](CausalSeed/LogTaylor.lean#L105), [`LogGauss.ladder`](CausalSeed/LogTaylor.lean#L59), [`LogGauss.majorant_scaled`](CausalSeed/LogTaylor.lean#L205)
- [`LogGauss.spatial`](CausalSeed/LogResidual.lean#L308), [`LogGauss.dFx_eq`](CausalSeed/LogResidual.lean#L741), [`LogGauss.time_taylor`](CausalSeed/LogResidual.lean#L716)
- [`LogGauss.residual_pointwise`](CausalSeed/LogResidual.lean#L764), [`LogGauss.residual_majorant`](CausalSeed/LogResidual.lean#L817)

**Theorem 40 (sharp logarithmic coefficient).** Let the increment family be centered with
common variance $`v>0`$ and put $`c=(\kappa_+-\kappa_-)/(3v\sqrt{2\pi e})`$. There is a
constant $`C`$, depending on the family, such that for all $`n\ge16`$

```math
\int_{\mathbb R}\Bigl|G_n(x)-\Phi\Bigl(\frac{x-c\ln n}{\sqrt{vn}}\Bigr)\Bigr|\,dx
\le C\sqrt{\ln n\,\ln\ln n},\qquad
|e_n-c\ln n|\le C\sqrt{\ln n\,\ln\ln n}.
```

The left integral is $`W_1(\nu_n,N(c\ln n,vn))`$ written as the $`L^1`$ distance of the two
distribution functions. That identity is the standard one-dimensional formula and is not itself
formalized: the Lean statement is the CDF form. The explicit threshold $`n\ge16`$ replaces
"as $`n\to\infty`$"; it makes $`\ln\ln n>1`$.

The proof follows the manuscript. Put $`t_0=\ln n`$, $`R^2=\tfrac83\ln t_0`$ and
$`A=\sqrt{vt_0}\,R+|c\ln t_0|`$. The truncated profile $`\tilde b`$ is $`0`$ below $`-A`$,
$`\Phi(z_{t_0})`$ on $`[-A,A)`$ and $`1`$ from $`A`$ on. Monotonicity and translation
invariance of $`T`$ give $`T^n\tilde b(\cdot-A)\le G_n\le T^n\tilde b(\cdot+A)`$, and for a
nondecreasing $`\beta`$ with values in $`[0,1]`$, $`\int(\beta(x+h)-\beta(x))\,dx\le h`$. So
$`\|G_n-T^n\tilde b\|_1\le2A`$. The Chernoff bounds $`\Phi(z)\le e^{\lambda z+\lambda^2/2}`$
and $`1-\Phi(z)\le e^{-\lambda z+\lambda^2/2}`$ ($`\lambda\ge0`$) dominate
$`|\tilde b-u_{t_0}|`$ by $`(t_0^{-1}+K_Bt_0^{-1/2})E(z_{t_0})`$. Integrated stability
(Theorem 36), propagation with Theorem 39, the width bound $`w_n=O(\ln n)`$ and
$`\sum_j(t_0+j)^{-3/2}\le2(t_0-1)^{-1/2}`$ give the comparison with $`u_{t_0+n}`$. Removing the
corrector, the $`L^1`$ scale comparison $`\|\Phi(\cdot/s_2)-\Phi(\cdot/s_1)\|_1\le2\phi(0)(s_2-s_1)s_2/s_1`$
and the shift comparison $`\|\Phi(\cdot-m_1)-\Phi(\cdot-m_2)\|_1\le|m_1-m_2|`$ finish the
$`L^1`$ bound. The mean follows from $`\int(H-\Phi((x-m)/s))\,dx=m`$.

Lean:
- [`Sqrt.IncFamily.Tit_mono`](CausalSeed/LogFinal.lean#L18), [`Sqrt.IncFamily.Tit_translate`](CausalSeed/LogFinal.lean#L22), [`Sqrt.IncFamily.Tit_monotone`](CausalSeed/LogFinal.lean#L30)
- [`LogGauss.lintegral_shift_le`](CausalSeed/LogFinal.lean#L58), [`LogGauss.lintegral_G_sub_Tit_bt`](CausalSeed/LogFinal.lean#L473), [`LogGauss.abs_bt_sub_le`](CausalSeed/LogFinal.lean#L452)
- [`LogGauss.Phi_le_exp_mgf`](CausalSeed/LogFinal.lean#L135), [`LogGauss.one_sub_Phi_le_exp_mgf`](CausalSeed/LogFinal.lean#L150), [`LogGauss.integral_H_sub_Phi`](CausalSeed/LogFinal.lean#L249)
- [`LogGauss.lintegral_Phi_scale`](CausalSeed/LogFinal.lean#L341), [`LogGauss.lintegral_Phi_shift`](CausalSeed/LogFinal.lean#L370), [`LogGauss.sum_pow_three_halves`](CausalSeed/LogFinal.lean#L379)
- [`LogGauss.main_L1`](CausalSeed/LogFinal.lean#L524), [`LogGauss.main_mean`](CausalSeed/LogFinal.lean#L829), with [`LogGauss.cdrift_eq`](CausalSeed/LogResidual.lean#L267) for the value of $`c`$

**Theorem 41 (sharp coefficient for the seed entropy).** For a finite stationary kernel
whose action laws $`P_i`$ have common entropy $`h`$ and common information variance $`v>0`$, put
$`\kappa_i=\mathbb E(-\log_2P_i(Y_i)-h)^3`$. There is $`C`$ such that for all $`n\ge16`$

```math
\Bigl|C_n-nh-\frac{\kappa_+-\kappa_-}{3v\sqrt{2\pi e}}\ln n\Bigr|\le C\sqrt{\ln n\,\ln\ln n}
```

(bits), and the same for the envelope mean $`L_n`$ and for any sequence within a bounded
additive amount of $`L_n`$. The proof uses $`L_n-nh=e_n`$, Theorem 40 and the sandwich
$`L_n\le C_n\le L_n+c_\star`$. For the dyadic pair of Proposition 35, $`C_n=L_n`$ at every
horizon and the coefficient is $`2/(3\sqrt{2\pi e})`$. The manuscript's clause about exact
seeds is stated for an arbitrary real sequence $`s_n`$ with $`|s_n-L_n|\le D`$.

Lean:
- [`Kernel.cost_sharp`](CausalSeed/LogCost.lean#L31), [`Kernel.near_envelope_sharp`](CausalSeed/LogCost.lean#L57)
- [`Kernel.LogPair.cost_sharp`](CausalSeed/LogCost.lean#L102), with [`Kernel.LogPair.isDyadic`](CausalSeed/LogCost.lean#L80),
  [`Kernel.LogPair.kmax_eq`](CausalSeed/LogCost.lean#L83), [`Kernel.LogPair.kmin_eq`](CausalSeed/LogCost.lean#L91)

### X. The bounded logarithmic remainder

The manuscript [`bounded_log_remainder`](bounded_log_remainder.tex) improves the remainder in
Theorems 40 and 41 from $`O(\sqrt{\ln n\ln\ln n})`$ to $`O(1)`$. Throughout,
$`\gamma_t(x)=(vt)^{-1/2}\varphi(x/\sqrt{vt})`$ is the centered Gaussian density of variance
$`vt`$, $`T`$ is the one-step Bellman operator of the centered surprisal family and $`U`$ its
monotone, subadditive and positively homogeneous majorant. The hypotheses are those of Theorem 40:
a centered increment family with common variance $`v>0`$.

**Theorem 42 (Gaussian defect).** There is $`D\ge0`$ such that for all $`t\ge1`$
$`|T_{\max}\gamma_t-\gamma_{t+1}|\le D\,t^{-3/2}\gamma_{8t}`$ pointwise. The window
constant is $`D_E=64^4e^{-63/16}=\max_{y\ge0}(1+y)^4e^{-y/16}`$, and the
majorant $`E`$ of the corrector satisfies $`E(z)\le D_Ee^{-z^2/16}`$.

Lean:
- [`LogGauss.defect`](CausalSeed/LogBounded.lean#L352), [`LogGauss.DE`](CausalSeed/LogBounded.lean#L100), [`LogGauss.pow_four_mul_exp_le`](CausalSeed/LogBounded.lean#L105), [`LogGauss.Emaj_le_DE`](CausalSeed/LogBounded.lean#L119)

**Theorem 43 (bounded amplification).** Let $`A\ge2`$ with $`6D\le\sqrt A`$ (in the proof,
$`A=2+36D^2`$). Then $`\int U^n\gamma_t\le2`$ for every $`n\ge0`$ and every $`t\ge A`$. The
proof is by strong induction on $`n`$ through the Gaussian telescoping
$`U^n\gamma_t\le\gamma_{t+n}+D\sum_{r<n}(t+r)^{-3/2}U^{n-1-r}\gamma_{8(t+r)}`$. Consequently
$`\|T^nf-T^ng\|_1\le2b`$ whenever $`|f-g|\le b\,\gamma_t(\cdot-m)`$ with $`t\ge A`$.

Lean:
- [`LogGauss.telescope`](CausalSeed/LogBounded.lean#L411), [`LogGauss.amp_bounded`](CausalSeed/LogBounded.lean#L447), [`LogGauss.amp_gauss`](CausalSeed/LogBounded.lean#L520), [`LogGauss.stability_gauss`](CausalSeed/LogBounded.lean#L543)

**Theorem 44 (Gaussian inputs).** With $`u_t`$ the corrected profile of Theorem 39, there is
$`b_0`$ (namely $`K_0D_E\sqrt{16\pi v}`$) with
$`|u_{t+1}-Tu_t|\le b_0t^{-3/2}\gamma_{8t}(\cdot-c\ln t)`$ for $`t\ge1`$. For each fixed
$`T_0\ge1`$ there is $`b_1`$ with $`|H-u_{T_0}|\le b_1\gamma_{8T_0}(\cdot-c\ln T_0)`$, where $`H`$ is
the unit step. Propagation then gives $`\|T^nu_{T_0}-u_{T_0+n}\|_1\le4b_0`$ for $`T_0\ge A`$.

Lean:
- [`LogGauss.residual_gauss`](CausalSeed/LogBounded.lean#L571), [`LogGauss.initial_gauss`](CausalSeed/LogBounded.lean#L598), [`LogGauss.propagation_bounded`](CausalSeed/LogBounded.lean#L679)

**Theorem 45 (bounded remainder).** There is $`K`$ such that for every $`n\ge1`$

```math
\int_{\mathbb R}\Bigl|G_n(x)-\Phi\Bigl(\frac{x-c\ln n}{\sqrt{vn}}\Bigr)\Bigr|\,dx\le K,
\qquad |e_n-c\ln n|\le K .
```

The first bound is the $`W_1`$ distance between $`\nu_n`$ and $`N(c\ln n,vn)`$ in its CDF
form. The proof chains stability from $`H`$ to $`u_A`$ ($`2b_1`$), propagation ($`4b_0`$), removal
of the corrector ($`K_B\sqrt v\int E`$), the scale change $`\sqrt{v(A+n)}\to\sqrt{vn}`$
($`2\varphi(0)\sqrt v\,A`$) and the shift $`c\ln(A+n)\to c\ln n`$ ($`|c|A`$).

Lean:
- [`LogGauss.bounded_L1`](CausalSeed/LogBounded.lean#L737), [`LogGauss.bounded_mean`](CausalSeed/LogBounded.lean#L840)

**Theorem 46 (bounded remainder for the seed entropy).** Under the hypotheses of Theorem 41
there is $`K`$ such that for every $`n\ge1`$

```math
\Bigl|C_n-nh-\frac{\kappa_+-\kappa_-}{3v\sqrt{2\pi e}}\ln n\Bigr|\le K
```

(bits), and the same for $`L_n`$. Hence $`C_n=nh+c\ln n+O(1)`$. For the dyadic pair of
Proposition 35, $`C_n=L_n`$ and $`|C_n-7n/2-\tfrac{2}{3\sqrt{2\pi e}}\ln n|\le K`$ for all
$`n\ge1`$. Numerically (half-bit lattice Bellman recursion) $`e_n-c\ln n`$ equals
0.6086, 0.6238, 0.6253, 0.6254 at $`n=10,10^2,10^3,10^4`$.

Lean:
- [`Kernel.cost_bounded`](CausalSeed/LogBounded.lean#L878), [`Kernel.LogPair.cost_bounded`](CausalSeed/LogBounded.lean#L905)


### XI. Sparse-activity entropy identities

The note *The Entropy Cost of Vanishing Activity* constructs, for a time-inhomogeneous
binary process whose success probabilities are at most $`p_t\in(0,1/2]`$, an explicit
countable coordinate whose entropy is $`h_2(p_t)+2p_t`$. The quantitative identities
behind that coordinate are formalized in namespace `Vanishing`. They do not use the
tree or seed types of `CausalSpectrum`.

**Theorem 47 (geometric seed).** The law $`P(k)=2^{-k}`$ on the positive integers has
Shannon entropy exactly $`2`$ bits.

**Theorem 48 (explicit coordinate).** For every $`0<p<1`$ the law
$`P(0)=1-p`$, $`P(k)=p\cdot 2^{-k}`$ ($`k\ge 1`$) is a probability measure and has
Shannon entropy $`h_2(p)+2p`$.

**Theorem 49 (finite excess).** For a finite family of real numbers $`(p_i)`$,

```math
\Bigl(\sum_i\bigl(h_2(p_i)+2p_i\bigr)\Bigr)-\sum_i h_2(p_i)=2\sum_i p_i.
```

If every $`p_i\ge 0`$, the left-hand difference is nonnegative, so the sum of the
coordinate entropies is at least the Bernoulli lower bound $`\sum_i h_2(p_i)`$.

**Theorem 50 (comparison).** On $`(0,1/2]`$, $`h_2(p)\ge p`$. Consequently, for a
sequence with $`0<p_t\le 1/2`$, summability of $`h_2(p_t)`$ implies summability of
$`p_t`$.

Lean:
- [`Vanishing.geometric_entropy`](CausalSeed/Vanishing.lean#L85)
- [`Vanishing.sparseCoordinate_entropy`](CausalSeed/Vanishing.lean#L115)
- [`Vanishing.zProb_tsum`](CausalSeed/Vanishing.lean#L109)
- [`Vanishing.sparseActivity_excess`](CausalSeed/Vanishing.lean#L179)
- [`Vanishing.h2_ge_self`](CausalSeed/Vanishing.lean#L153)
- [`Vanishing.summable_prob_of_summable_h2`](CausalSeed/Vanishing.lean#L174)

[`VanishingEmbed.shannonTerm_group`](CausalSeed/VanishingEmbed.lean) and
[`VanishingEmbed.entropy_prod`](CausalSeed/VanishingEmbed.lean) are the two analytic
steps of the finite-horizon sandwich: merging masses cannot raise the Shannon sum, and a
product of two laws has entropy equal to the sum of the factors.

Also checked, still without a strategy space:
[`Vanishing.gate_exact`](CausalSeed/Vanishing.lean) turns a binary expansion of $`q/p`$
into response probability $`q`$; [`Vanishing.prod_one_sub_tendsto_zero`](CausalSeed/Vanishing.lean)
sends $`\prod(1-p_t)`$ to $`0`$ when $`\sum p`$ diverges;
[`Vanishing.one_sub_listProd_le_sum`](CausalSeed/Vanishing.lean) is the union bound
$`1-\prod(1-x)\le\sum x`$; and
[`Vanishing.fairBit_image_ne_quarter`](CausalSeed/Vanishing.lean) with
[`Vanishing.endpoint_entropy_three_halves`](CausalSeed/Vanishing.lean) show that a function
of one fair bit cannot have success probability $`1/4`$, while the three-atom law
$`(1/2,1/4,1/4)`$ has entropy $`3/2`$.

**Theorem 51 (maximizing readout).** For $`0<p_t<1`$ on a finite horizon, the independent
Bernoulli vector has entropy $`\sum h_2(p_t)`$, and the product of the geometric gates
has entropy $`\sum(h_2(p_t)+2p_t)`$. Let $`C_n`$ be the infimum of Shannon entropies of
countable laws equipped with a deterministic readout of that Bernoulli vector. Then

```math
\sum_t h_2(p_t)\;\le\;C_n\;\le\;\sum_t\bigl(h_2(p_t)+2p_t\bigr).
```

This $`C_n`$ is the cost of the maximizing bits only. It is not an infimum over
history-indexed adaptive policies.

**Theorem 52 (divergence obstructions).** Let $`0<p_t\le 1/2`$. If $`\sum p_t`$ diverges,
no countable nonnegative law of mass one reproduces every finite maximizing transcript.
If $`\sum h_2(p_t)`$ diverges, no countable readout of all those finite transcripts has
finite entropy. The existence halves are not formalized: a countable seed when
$`\sum p<\infty`$, and finite entropy when $`\sum h_2<\infty`$.

**Theorem 53 (finite last-event identity).** For a finite list of probabilities in
$`[0,1]`$, written newest first,

```math
\sum h_2(p)-H(\mathrm{lastLaw}\,p)=\mathrm{hiddenEntropy}\,p.
```

`cost_last_event_bounds` only moves an assumed entropy sandwich across this identity.
It is not a theorem about a controlled tree.

Lean:
- [`Vanishing.bernJoint_entropy`](CausalSeed/VanishingClose.lean#L100)
- [`Vanishing.seed_entropy`](CausalSeed/VanishingClose.lean#L308)
- [`Vanishing.activity_sandwich`](CausalSeed/VanishingClose.lean#L575)
- [`Vanishing.no_countable_seed_of_divergent`](CausalSeed/VanishingClose.lean#L595)
- [`Vanishing.no_finite_entropy_of_divergent_h2`](CausalSeed/VanishingClose.lean#L668)
- [`Vanishing.LastEvent.last_event_identity`](CausalSeed/VanishingLastEvent.lean#L121)

Not formalized: history-indexed strategies, cylinder exactness for every adaptive policy,
one measure on all response tables, total-variation approximation of strategy laws, and the
$`\log_2\ln n`$ asymptotic. Those statements remain mathematical claims of the note,
not Lean theorems.

### XII. Finite locality and a capacity-scale bound

The notes *An Unbounded Entropy Cost of Localizing a Decoder*,
*Identical Information Spectra, Different Causal Feasibility*,
*A Sharp Entropy–Accuracy Threshold for Local Simulation* and
*Atomic Capacity Does Not Determine Sublinear Causal Entropy Growth* are not
Lean-certified as written. The finite statements below are.

**Theorem 54 (pairwise fair bits).** The uniform law on four points has Shannon
entropy $`2`$. A finite seed pushed onto that law has entropy at least $`2`$.
Every finite law of pairwise independent fair bits on $`n`$ coordinates has atoms
of mass at most $`1/(n+1)`$ and Shannon entropy at least $`\log_2(n+1)`$. The gap
$`\log_2(n+1)-2`$ is unbounded in $`n`$. The subtracted $`2`$ is the entropy of the
centralized four-point seed, not a theorem that $`C_{\mathrm{central}}(W_m)=2`$
for the behavior $`W_m`$.

**Theorem 55 (finite CHSH obstruction).** Every deterministic local CHSH table
takes a value in $`\{-2,2\}`$, so no finite convex combination equals $`4v`$ when
$`v>1/2`$. The mixture $`(3/4)\cdot 1+(1/4)\cdot(-1)`$ has correlation $`1/2`$,
and $`h_2(1/4)=2-(3/4)\log_2 3`$.

**Theorem 56 (uniform block and mixture error).** The uniform law on $`\{0,1\}^k`$
has Shannon entropy $`k`$, and any $`K`$ of its atoms have total mass at most
$`K\cdot 2^{-k}`$. On $`[0,1]`$, $`h_2\le 1`$. If $`0\le a\le 1`$, $`0\le H`$,
$`H\le\log_2(e(f+1))`$ and $`t\le f\le t+1`$, the number

```math
C=h_2(a)+a(f+H)+(1-a)t
```

satisfies $`-1\le C-f\le 1+a\log_2(e(f+1))`$. The bound $`H`$ and the floor proxy
$`t`$ are hypotheses. This is not a construction of the processes in that note,
and it is not $`\mathrm{atomQ}=a`$ or $`C_n\sim f(n)`$.

**Theorem 57 (exact local cost on a linear family).** Let $`m=2^k-1`$ with
$`k\ge 1`$. The uniform seed on $`\mathbb F_2^k`$, evaluated on the $`m`$
nonzero linear forms, is a finite law of pairwise independent fair bits, and
its Shannon entropy is exactly $`k=\log_2(m+1)`$. Every pairwise fair law on
these $`m`$ coordinates costs at least $`k`$, so the construction is optimal.
This is the matching upper bound from linear forms. It is not the existence of
a Hadamard matrix of order $`m+1`$, and it is not the approximate coefficient
$`(1-4\varepsilon)\log_2\log_2 m`$.

**Theorem 58 (finite record and scalar contraction).** One fair bit followed by
independent Bernoulli flips of probabilities $`p_t\in[0,1]`$ has Shannon entropy

```math
1+\sum_t h_2(p_t).
```

If $`0\le p_t\le 1/2`$, every atom of that law is at most
$`(1/2)\prod_t(1-p_t)`$. If $`0\le p_t<1`$, that cylinder is at most
$`(1/2)\exp(-\sum_t p_t)`$. The scalar recurrence
$`d_{j+1}\le q_{j+1}d_j+\varepsilon_{j+1}`$, with $`q_{j+1}\ge 0`$, iterates to

```math
d_n\le\Bigl(\prod_{j=1}^{n}q_j\Bigr)d_0+\sum_{k=1}^{n}\varepsilon_k\prod_{j=k+1}^{n}q_j.
```

If $`0\le q_j\le q<1`$, $`0\le\varepsilon_j\le\varepsilon`$ and $`d_0\ge 0`$, then

```math
d_n\le q^n d_0+\varepsilon\frac{1-q^n}{1-q}.
```

This is the finite identity behind $`C_n=1+\sum_j h_2(p_j)`$ and the scalar form
of the contraction bound in the closure note. It is not a quantum instrument,
not atomic capacity of an infinite-path law, not Borel--Cantelli, and not a
theorem that a finite prefix cannot identify infinite atomic capacity.

**Theorem 59 (exact decoding and one invariant orbit).** Let $`D_{\#}\mu=P`$.
For every measurable event $`B`$,

```math
\mu(D^{-1}(B))=P(B).
```

If $`P(B)>0`$, every exact decoder charges $`B`$. Two seeds with the same
pushforward charge every event equally; a one-point seed and a fair bit, both
decoded to a single outcome, are an instance. If $`x_0\in A`$, $`F(A)\subseteq A`$
and $`A\cap B=\emptyset`$, then $`F^n(x_0)\notin B`$ for every $`n\ge 0`$.
Exact decoding does not imply that orbit statement, and one missed orbit does
not set the mass of the missed event to zero. Neither statement is a theorem
about human invulnerability.

**Theorem 60 (questions, structure, and finite selection).** A response map
factors uniquely through the quotient by equal answers. A smaller question set
induces a surjection on classes, and no questions at all give one class on a
nonempty carrier. Future observations are the largest equivalence that preserves
the present observation and every transition. Every exact deterministic quotient
factors uniquely and surjectively onto that behavioral quotient, preserves
observations and transitions, and, when finite, has at least as many states.
An observation-based policy has the same transcript on the quotient. On a finite
nonempty state set, responses to words of length at most $`k`$ agree with
behavioral equivalence for some $`k<|S|`$. Equal present responses need not be a
congruence: on $`\{0,1,2\}`$ with $`o(0)=o(1)`$, $`o(2)`$ different, and
$`F(0)=0`$, $`F(1)=F(2)=2`$, one step separates $`0`$ from $`1`$.

If $`x`$ reaches $`y`$, every transition invariant agrees on them. Universal
reachability makes every invariant constant. Invariants are exactly the maps
constant on the undirected graph of the transitions. The sink $`F(0)=F(1)=1`$
on $`\{0,1\}`$ has only constant invariants, but $`1`$ does not reach $`0`$.
Universal reachability passes to the behavioral quotient. The converse fails
when the observation is constant and there are no actions. There is one map out
of the empty set and its image is empty. Maps out of a singleton are the
elements of the codomain. No point of a two-element set is fixed by every
bijection, so no choice of a point in every nonempty type is equivariant. A
permutation-invariant real weighting of an $`n`$-element set, $`n>0`$, which
sums to one, is uniform. Any nonnegative seed pushed forward onto that law has
Shannon entropy at least $`\log_2 n`$, and the uniform law attains the bound.
No summable real law on $`\mathbb{N}`$ which sums to one is invariant under
every permutation. Iterating $`X\cup R[X]`$ from $`\emptyset`$ stays empty; a
chosen source set need not. A finite product of independent laws, each summing
to one, has those laws as its coordinate marginals. If a finite set of control
transcripts of cardinality at most $`K`$ selects $`n`$ targets exactly, then
$`n\le K`$. The action that names its target reaches every state in one step.
Extending the state by a hidden coordinate does not change the observation
transcript of an observation-based policy.

Theorem 60 does not include an adaptive transcript law for a lumpable
stochastic kernel, agreement of one-seed costs, countable-seed existence,
atomic capacity, or Fano's inequality. It is not claimed to be new.

**Theorem 61 (observable identity and exact simulation).** The complete
response profile of a state is exactly the relation used to form the behavioral
quotient already constructed in Theorem 60. The quotient observation and
transitions are well-defined, and every adaptive policy produces the same
transcripts on the quotient as on the original system. An arbitrary hidden
extension (extra internal coordinate with arbitrary dynamics) produces exactly
the same observation transcripts. Exact deterministic decoding preserves the
probability of every measurable event (the pushforward identity of Theorem 59).
An invariant region disjoint from a forbidden set is never entered by any finite
action sequence; exact decoding does not by itself yield that statement.
A property of states factors through the response profile if and only if it is
constant on the fibers of the profile. The Gaussian fixed-point statement of
the accompanying note is recorded but not re-proved (Schwartz-space Fourier
analysis is not imported). The infinite-information remark (a uniform seed on
$[0,1)$ can encode infinitely many independent fair bits) is not a finite
discrete Shannon-entropy statement and is not formalized.

Theorem 61 does not establish consciousness transfer, an afterlife, or human
invulnerability. It is a synthesis of the constructions already present in
Theorems 59 and 60, together with the fiber-constancy criterion for
identifiability.

**Theorem 62 (exact sharing criterion).** For one prescribed finite joint law
$`\mu`$ on a product of two finite alphabets, every exact shared seed costs at
least $`H(\mu)`$, and the bound is attained by using $`\mu`$ itself as the seed
with the two coordinate projections as decoders. A deterministic function of a
finite law cannot increase its entropy. Two positive masses cost strictly more
apart than together.

Theorem 62 is the entropy identity for one fixed joint law. It does not
re-prove the chain rule, so the difference of the two minima is not identified
here with a conditional entropy, and the Fano upper bound is not re-proved. It
does not produce a causal shared seed for a family of adaptive transcript laws.
Changing the prescribed law is not an exact simulation of the original one.

**Theorem 63 (predictive stability is not small seed cost).** Total variation
on a finite alphabet is a pseudometric and is invariant under a bijection of
the alphabet. One-step predictive agreement is an equivalence relation; the
update by a common action and outcome descends to the quotient whenever the
kernel of an extension is determined by the kernel of its prefix. A kernel
that ignores its history identifies every pair of histories. The constant
kernel that emits a fair bit is completely stable, and the exact seed cost of
that one step is one bit.

Theorem 63 does not include the imported bound $`L(T_n)\le C(T_n)\le L(T_n)+c_\star`$,
an $`n`$-step product entropy, or any empirical claim about stillness. It is
not a statement about consciousness.

[`Vanishing.LastEvent.last_event_entropy_bounds`](CausalSeed/VanishingBridge.lean)
and [`Vanishing.Approximation.uniform_policy_event_bound`](CausalSeed/VanishingBridge.lean)
are finite interfaces for the wholeness and approximation notes: the last-success
deficit is at most an explicit majorant, and one shared mismatch set bounds the
event error of every policy in a finite family. The tail set of weight
$`\sum_{t>N}p_t`$ is not constructed.

Lean:
- [`LocalSeparation.central_entropy_ge_two`](CausalSeed/LocalSeparation.lean)
- [`LocalSeparation.atom_le`](CausalSeed/LocalSeparation.lean)
- [`LocalSeparation.pairwise_entropy_ge`](CausalSeed/LocalSeparation.lean)
- [`LocalSeparation.locality_gap_unbounded`](CausalSeed/LocalSeparation.lean)
- [`LocalSeparation.not_local_chsh_mixture`](CausalSeed/LocalSeparation.lean)
- [`LocalSeparation.h2_quarter`](CausalSeed/LocalSeparation.lean)
- [`CapacityScale.fairBlock_entropy`](CausalSeed/CapacityScale.lean)
- [`CapacityScale.fairBlock_heavy_mass`](CausalSeed/CapacityScale.lean)
- [`CapacityScale.h2_le_one`](CausalSeed/CapacityScale.lean)
- [`CapacityScale.mixture_scale_error`](CausalSeed/CapacityScale.lean)
- [`LinearLocal.f2_exact`](CausalSeed/LinearLocal.lean)
- [`LinearLocal.f2_optimal`](CausalSeed/LinearLocal.lean)
- [`ClosureScale.record_entropy`](CausalSeed/ClosureScale.lean)
- [`ClosureScale.record_atom_le`](CausalSeed/ClosureScale.lean)
- [`ClosureScale.record_cylinder_le_exp`](CausalSeed/ClosureScale.lean)
- [`ClosureScale.contraction_iterate`](CausalSeed/ClosureScale.lean)
- [`ClosureScale.uniform_contraction`](CausalSeed/ClosureScale.lean)
- [`EventFidelity.event_preserved`](CausalSeed/EventFidelity.lean)
- [`EventFidelity.positive_not_eliminated`](CausalSeed/EventFidelity.lean)
- [`EventFidelity.seed_change_preserves`](CausalSeed/EventFidelity.lean)
- [`EventFidelity.dirac_and_fair_agree`](CausalSeed/EventFidelity.lean)
- [`EventFidelity.unreachable_of_invariant`](CausalSeed/EventFidelity.lean)
- [`EventFidelity.exactness_does_not_give_unreachability`](CausalSeed/EventFidelity.lean)
- [`EventFidelity.missed_orbit_does_not_zero_mass`](CausalSeed/EventFidelity.lean)
- [`QuestionStructure.obs_factor`](CausalSeed/QuestionStructure.lean)
- [`QuestionStructure.behav_largest`](CausalSeed/QuestionStructure.lean)
- [`QuestionStructure.behavFactor_surjective`](CausalSeed/QuestionStructure.lean)
- [`QuestionStructure.behav_natCard_le`](CausalSeed/QuestionStructure.lean)
- [`QuestionStructure.rollout_quotient`](CausalSeed/QuestionStructure.lean)
- [`QuestionStructure.refine_stabilizes`](CausalSeed/QuestionStructure.lean)
- [`QuestionStructure.PresentNotCong.not_behav`](CausalSeed/QuestionStructure.lean)
- [`QuestionStructure.inv_iff_eqvGen`](CausalSeed/QuestionStructure.lean)
- [`QuestionStructure.Sink.not_reach`](CausalSeed/QuestionStructure.lean)
- [`QuestionStructure.reach_descends`](CausalSeed/QuestionStructure.lean)
- [`QuestionStructure.exact_selection_bound`](CausalSeed/QuestionStructure.lean)
- [`QuestionStructure.perm_invariant_uniform`](CausalSeed/QuestionStructure.lean)
- [`QuestionStructure.uniform_seed_entropy`](CausalSeed/QuestionStructure.lean)
- [`QuestionStructure.no_perm_invariant_nat`](CausalSeed/QuestionStructure.lean)
- [`QuestionStructure.product_marginal`](CausalSeed/QuestionStructure.lean)
- [`QuestionStructure.hidden_extension_transcript`](CausalSeed/QuestionStructure.lean)
- [`ObservableIdentity.quotient_preserves_transcripts`](CausalSeed/ObservableIdentity.lean)
- [`ObservableIdentity.hidden_extension_same_transcripts`](CausalSeed/ObservableIdentity.lean)
- [`ObservableIdentity.event_preservation`](CausalSeed/ObservableIdentity.lean)
- [`ObservableIdentity.invariant_region_criterion`](CausalSeed/ObservableIdentity.lean)
- [`ObservableIdentity.exactness_does_not_imply_invariance`](CausalSeed/ObservableIdentity.lean)
- [`ObservableIdentity.property_factors_implies_constant`](CausalSeed/ObservableIdentity.lean)
- [`ObservableIdentity.underdetermination`](CausalSeed/ObservableIdentity.lean)
- [`Sharing.sharing_criterion`](CausalSeed/Sharing.lean)
- [`Sharing.sharing_attained`](CausalSeed/Sharing.lean)
- [`Sharing.entropy_of_function`](CausalSeed/Sharing.lean)
- [`Sharing.entTerm_add_lt`](CausalSeed/Sharing.lean)
- [`Stillness.tv_triangle`](CausalSeed/Stillness.lean)
- [`Stillness.tv_bijection`](CausalSeed/Stillness.lean)
- [`Stillness.update_well_defined`](CausalSeed/Stillness.lean)
- [`Stillness.ignore_history_stable`](CausalSeed/Stillness.lean)
- [`Stillness.fair_stable_not_free`](CausalSeed/Stillness.lean)

Not formalized, in addition to the list at the end of Section XI: the sharp
coefficient $`(1-4\varepsilon)\log_2\log_2 m`$, a matching local upper bound for
every $`m`$ rather than the linear family $`m=2^k-1`$, equivalence with a
Hadamard matrix, the
locality statements for countable seeds, the entropy-rate triangle
$`0\le R\le 1-a`$, $`C_{\mathrm{app}}(\varepsilon)=\log_2(1/\varepsilon)+O(1)`$,
the total-variation distance of $`Q_v`$ from the local set, and the realization
$`\mathrm{atomQ}=a`$, $`C_n\sim f(n)`$. Theorem 58 does not include a quantum
instrument, atomic capacity of an infinite-path law, or Borel--Cantelli.
Theorem 59 is the pushforward identity and one invariant orbit. It is not a
theorem about human invulnerability. Theorem 60 is the observable quotient,
the deterministic behavioral quotient, finite word-length stabilization,
reachability of invariants, the empty-input and symmetry facts, the uniform
seed bound, the product marginal, the support bound $`n\le K`$, and hidden
extensions. It is not a lumpable stochastic transcript law, not atomic
capacity, and not Fano's inequality.

## Verification

The development is the import closure of
[`CausalSeed/Main.lean`](CausalSeed/Main.lean), together with
[`CausalSeed/Vanishing.lean`](CausalSeed/Vanishing.lean),
[`CausalSeed/VanishingEmbed.lean`](CausalSeed/VanishingEmbed.lean),
[`CausalSeed/VanishingClose.lean`](CausalSeed/VanishingClose.lean),
[`CausalSeed/VanishingLastEvent.lean`](CausalSeed/VanishingLastEvent.lean),
[`CausalSeed/VanishingBridge.lean`](CausalSeed/VanishingBridge.lean),
[`CausalSeed/LocalSeparation.lean`](CausalSeed/LocalSeparation.lean),
[`CausalSeed/CapacityScale.lean`](CausalSeed/CapacityScale.lean),
[`CausalSeed/LinearLocal.lean`](CausalSeed/LinearLocal.lean) and
[`CausalSeed/ClosureScale.lean`](CausalSeed/ClosureScale.lean),
[`CausalSeed/EventFidelity.lean`](CausalSeed/EventFidelity.lean) and
[`CausalSeed/QuestionStructure.lean`](CausalSeed/QuestionStructure.lean),
imported by [`CausalSeed.lean`](CausalSeed.lean) and not by `Main`. Pinned toolchain:

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

[`AXIOMS.txt`](AXIOMS.txt) records the result of the 12 October audit of the
`Main` import closure. All **2528** theorems in those 106 project modules depend only
on `propext`, `Classical.choice` and `Quot.sound`; seven depend on no axiom. No theorem
uses `sorryAx`, that build reports no `sorry` or `admit`, and the project declares no
`axiom`.

`CausalSeed/Vanishing.lean` was added on 19 October, after that audit.
`VanishingBridge`, `LocalSeparation` and `CapacityScale` were added on 20 October.
Each builds with `lake build`, contains no `sorry` or `admit`, and declares no
`axiom`. A full re-audit including these modules has not been run. `AXIOMS.txt`
remains the 12 October listing of the `Main` import closure.

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
| `Kernel.sub`, `Kernel.Dominates`, `Kernel.H` | [MaxEntropy.lean#L27](CausalSeed/MaxEntropy.lean#L27), [#L60](CausalSeed/MaxEntropy.lean#L60), [#L174](CausalSeed/MaxEntropy.lean#L174) | the kernel of the actions in `S`; $`\mathbb E e^{\theta I_j}\,\mathbb E e^{-\theta I_{i_0}}\le1`$ for `j ∉ S`; `H(K_a)` in bits |

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

**Maximal-entropy reduction**
- `MaxEntropyHoeffding`: Hoeffding's lemma for finite weighted averages.
- `MaxEntropy`: the subkernel of a set of actions, exponential domination, the comparison of envelopes, means and costs, and restriction of seeds (Theorems 28 and 29).
- `MaxEntropyReduction`: the reduction to the maximizing subfamily and the dichotomy between $`\sqrt n`$ and logarithmic growth (Theorem 30, Corollary 31).
- `MaxEntropyExample`: the three dyadic laws $`P,Q,R`$ (Proposition 32).

**Logarithmic coefficient**
- `LogWidth`: the width bound without nondegeneracy hypothesis, integrated amplification, stability and propagation (Theorems 33 and 34).
- `LogExample`: the dyadic pair $`P,Q`$ and the coefficient bounds (Proposition 35).
- `LogAmp`: amplification, stability and propagation under $`C^1`$ majorants (Theorem 36).
- `LogGauss`: the Gaussian density, its derivatives, exact $`L^1`$ norms and scaling (Theorem 37).
- `LogCorrector`: the forcing, the resonant mass $`a`$, the corrector $`B`$, its ODE and tail bounds (Theorem 38).
- `LogTaylor`: $`\Phi`$, the mean-value ladder, the Gaussian window lemma and the majorant profile $`E`$.
- `LogResidual`: the coefficient and forcing links, Taylor expansions and the residual lemma (Theorem 39).
- `LogFinal`: the sandwich, Chernoff bounds, Gaussian `L¹` comparisons, the choice of $`t_0`$ and the sharp coefficient (Theorem 40).
- `LogCost`: the sharp coefficient for $`C_n`$ and $`L_n`$, and the dyadic pair (Theorem 41).
- `LogBounded`: the Gaussian defect, bounded amplification, Gaussian inputs and the bounded remainder (Theorems 42 to 46).

**Sparse activity**
- `Vanishing`: the geometric entropy identity $`H=2`$, the explicit coordinate
  entropy $`h_2(p)+2p`$, the finite excess $`2\sum p_i`$, and the comparison
  $`h_2(p)\ge p`$ on $`(0,1/2]`$ (Theorems 47 to 50).
- `VanishingEmbed`: grouping and the entropy of a product of laws.
- `VanishingClose`: the maximizing-bit sandwich and the two divergence obstructions
  (Theorems 51 and 52). Not adaptive policies, and not the existence half of the trichotomy.
- `VanishingLastEvent`: the finite last-event identity (Theorem 53). Not an infinite
  causal simulation.
- `VanishingBridge`: the last-success deficit bound and one shared mismatch bound
  for a finite family of policies. Not the tail $`\sum_{t>N}p_t`$.
- `LocalSeparation`: the finite pairwise-fair lower bound and the finite CHSH
  obstruction (Theorems 54 and 55). Not the sharp locality coefficient, and not
  a Hadamard equivalence.
- `CapacityScale`: entropy of a uniform binary block, the heavy-atom mass bound,
  $`h_2\le 1`$, and the numerical mixture-error shape (Theorem 56). Not
  $`\mathrm{atomQ}`$ and not $`C_n\sim f(n)`$.
- `LinearLocal`: the exact local cost $`k` for $`m=2^k-1`$ pairwise fair bits
  (Theorem 57). Not a Hadamard matrix, and not the approximate coefficient.
- `ClosureScale`: the finite record entropy $`1+\sum h_2(p_t)`$, the cylinder
  bound, and the scalar contraction (Theorem 58). Not a quantum instrument, and
  not atomic capacity of an infinite-path law.
- `EventFidelity`: exact decoding preserves event probabilities, and an
  invariant set keeps its orbit out of a disjoint set (Theorem 59). Not human
  invulnerability. The two statements do not imply each other.
- `QuestionStructure`: observable and behavioral quotients, finite word-length
  stabilization, reachability of invariants, empty and symmetric inputs, the
  uniform seed bound, product marginals, the support bound $`n\le K`$, and
  hidden extensions (Theorem 60). Not a lumpable stochastic transcript law,
  not atomic capacity, and not Fano's inequality.

**Mathematical expositions** (LaTeX/PDF at the repository root)
- `bellman_square_root`: the square-root asymptotic.
- `sharp_logarithmic_coefficient`: the logarithmic coefficient (formalized as Theorems 36 to 41).
- `bounded_log_remainder`: the bounded remainder (formalized as Theorems 42 to 46).
- `universal_causal_seed`: the Rényi spectrum.
- `atomic_capacity`: atomic capacity.
- `completion_proof`: infinite seeds and entropy attainment.
- `arithmetic_causality`: arithmetic rigidity.
- `causal_spectrum.pdf`, `one_seed_entropy.pdf`.
- `Entropy_Cost_of_Vanishing_Activity.pdf`, `bounded_excess_binary.pdf`,
  `Wholeness_as_Lossless_Causal_Compression.pdf`, `optimal_causal_approximation.pdf`:
  Theorems 47 to 53 and the finite bridge in `VanishingBridge`. Not adaptive
  trees, not $`\log_2\ln n`$, and not $`C_{\mathrm{app}}(\varepsilon)`$.
- `Identical_Information_Spectra__Different_Causal_Feasibility.pdf`: Theorems 54
  and 55 only. Not the distance of $`Q_v`$ from the local set.
- `atomic_capacity_entropy_rate.pdf`: the entropy-rate triangle. Not formalized.
- `Atomic_Capacity_Does_Not_Determine_Sublinear_Causal_Entropy_Growth.pdf`:
  Theorem 56 only. Not $`\mathrm{atomQ}=a`$ and not $`C_n\sim f(n)`$.
- `Full_Support_Regularization_with_Uniform_Entropy_Control.pdf`: not formalized.
  The seed identity $`H=h_2(p)+2p`$ used in its construction is Theorem 48.
- `Unbounded_Failure_of_Horizonwise_Optimality_for_Exact_Causal_Seeds.pdf`:
  not formalized.
- `closure_atomic_capacity_one_seed.pdf`: Theorem 58 is the finite identity
  $`1+\sum h_2(p_t)`$ and the scalar contraction bound only. Not a quantum
  instrument, not atomic capacity of an infinite-path law, and not
  Borel--Cantelli. The countable seed in its construction is the coordinate of
  Theorem 48, whose entropy is $`h_2(p)+2p`$. The perturbation, preservation of
  atomic mass, and the uniform-positivity lower bound $`nh_{\min}`$ are not
  Lean theorems.
- `questions_structure_causal_simulation.pdf`: Theorem 60 is the observable
  quotient, the deterministic behavioral quotient and its transcripts, finite
  stabilization, the reachability obstruction, empty and symmetric inputs, the
  uniform seed bound, independent finite marginals, the support bound
  $`n\le K`$, and hidden extensions. Not the adaptive lumpability law, not
  agreement of one-seed costs or atomic capacity, and not Fano's inequality.
  Theorem 59 is the separate pushforward identity and one invariant orbit,
  not this note.
- The sharp locality coefficient $`(1-4\varepsilon)\log_2\log_2 m`$ is not formalized.

## Scope and open problems

**Scope.**
- All local alphabets are finite and nonempty.
- Policies are deterministic and adaptive.
- Theorems 3, 14, 22 and Corollary 23 and the nonnegative-kernel parts of Theorems 15 and 16
  allow zero kernel entries; all other results assume strictly positive kernels.

**Open mathematical problems.**
- The exact value of $`G_{\ast}\in[\tfrac29,c_{\star}]`$, and whether all minimizers are causal
  at $`\kappa=G_{\ast}`$.
- The constant term of the sharp logarithmic expansion. Theorems 45 and 46 show
  $`C_n-nh-\frac{\kappa_+-\kappa_-}{3v\sqrt{2\pi e}}\ln n=O(1)`$ for equal entropies and
  variances. Whether this bounded sequence converges, and to which constant, is open (for the
  pair of Proposition 35 the numerics suggest $`e_n-c\ln n\to0.6254\ldots`$). For a kernel with
  unequal entropies, Theorem 29 relates $`C_n`$ to its maximizing subfamily only up to
  $`O(\log n)`$, so the coefficient is not transferred there.
- Whether $`C_n-C^{\ast}_n`$ in Theorem 29 is bounded when several actions attain the
  maximal entropy (Theorem 19 gives this for one maximizing action).
- Optimality of the constants $`c_{\star}`$ and $`d_\alpha`$.
- History-indexed strategies, cylinder exactness for every adaptive policy, one
  measure on all response tables, total-variation approximation, and the
  $`\log_2\ln n`$ asymptotic of the vanishing-activity note. Theorems 51 and 52
  are the maximizing-bit sandwich and the two divergence obstructions. Theorem 53
  is the finite last-event identity. Theorems 54 and 55 are the finite locality
  obstructions. Theorem 56 is the uniform-block identity and the numerical
  mixture bound, not the realization $`\mathrm{atomQ}=a`$, $`C_n\sim f(n)`$.
  Theorem 57 is the exact linear-form cost for $`m=2^k-1`$, not a Hadamard
  equivalence. Theorem 58 is the finite record identity and the scalar
  contraction, not a quantum instrument and not an infinite-path capacity.
  Theorem 59 is the pushforward identity and one invariant orbit, not a
  statement about human invulnerability. Theorem 60 is the deterministic
  quotient, the finite selection bound $`n\le K`$, and the symmetry facts in
  the questions note. It is not Fano's inequality and not a lumpable
  stochastic transcript law. Theorem 61 is the synthesis of observable identity,
  event preservation, the invariant-region criterion, and the fiber-constancy
  criterion for property identifiability. It is not a claim about consciousness
  transfer, an afterlife, or human invulnerability, and it does not re-prove the
  Gaussian Fourier fixed point. Theorem 62 is the entropy identity for one
  finite joint law: the minimum exact shared-seed entropy equals the entropy
  of the law. It does not re-prove the chain rule or the Fano upper bound, and
  it is not a causal shared seed. Theorem 63 is predictive equivalence,
  invariance of total variation under a bijection, and the fair-bit
  counterexample that stability does not force a small seed cost. It does not
  include the bound $`L\le C\le L+c_\star`$ and it is not a statement about
  consciousness.
  A countable seed when $`\sum p`$ converges,
  and finite entropy when $`\sum h_2`$ converges, are not formalized.

**Hypotheses of Theorem 16.** Parts 1 and 2 require a reference action whose law has two
distinct values and whose variance (and, for part 2, third moment) every action shares.
The excluded case, in which every action is a point mass, is not covered by the formal
statement. Likewise, part 2 of Corollary 31 does not cover the case in which every action
of $`S`$ is uniform.

## Attribution

The additive constant and the nonlinear diffusion profile have antecedents in the
literature. This repository does not claim originality or priority. Its purpose is to
state the causal simulation results precisely and to provide formal proofs.
Comparison with prior work is a separate task.
