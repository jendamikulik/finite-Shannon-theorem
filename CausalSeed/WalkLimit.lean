/-
Negative drift: the monotone limit of `E M_n`, exponential tail bounds, and the corollary for
the optimal causal seed entropy of a dyadic two-action kernel.
-/
import CausalSeed.WalkEnvelope

noncomputable section
open Classical Finset Filter
open scoped Topology

namespace CausalSpectrum.Walk
namespace Law
variable (W : Law)

theorem ESp_nonneg (k : ℕ) : 0 ≤ W.ESp k := W.E_nonneg k fun _ => le_max_right _ _

theorem EM_mono : Monotone W.EM := by
  refine monotone_nat_of_le_succ fun n => ?_
  rw [EM_succ]
  have := W.ESp_nonneg (n + 1)
  have : 0 ≤ W.ESp (n + 1) / (n + 1) := by positivity
  linarith

theorem E_mono_seq (n : ℕ) {f g : (ℕ → ℝ) → ℝ}
    (h : ∀ ys : Fin n → Fin W.k, f (W.seq ys) ≤ g (W.seq ys)) : W.E n f ≤ W.E n g :=
  sum_le_sum fun ys _ => mul_le_mul_of_nonneg_left (h ys) (wgt_nonneg ys)

/-- The Spitzer terms `E(S_k)_+ / k`, `k ≥ 1`. -/
def term (j : ℕ) : ℝ := W.ESp (j + 1) / (j + 1)

theorem term_nonneg (j : ℕ) : 0 ≤ W.term j := by
  have := W.ESp_nonneg (j + 1); unfold term; positivity

theorem EM_eq_sum (n : ℕ) : W.EM n = ∑ j ∈ range n, W.term j := W.spitzer n

/-- **Tail bound.** If `E(S_k)_+ ≤ c λ^k` with `0 ≤ λ < 1`, the Spitzer series converges, its sum
`ℓ` is the increasing limit of `E M_n`, and `0 ≤ ℓ - E M_n ≤ c λ^{n+1} / ((n+1)(1-λ))`. -/
theorem tail_bound {c lam : ℝ} (hc : 0 ≤ c) (hl0 : 0 ≤ lam) (hl1 : lam < 1)
    (hb : ∀ k, W.ESp k ≤ c * lam ^ k) :
    Summable W.term ∧ Tendsto W.EM atTop (𝓝 (∑' j, W.term j)) ∧
      (∑' j, W.term j) = ⨆ n, W.EM n ∧
      ∀ n, 0 ≤ (∑' j, W.term j) - W.EM n ∧
        (∑' j, W.term j) - W.EM n ≤ c * lam ^ (n + 1) / ((n + 1) * (1 - lam)) := by
  have hle : ∀ j, W.term j ≤ c * lam ^ (j + 1) := fun j => by
    unfold term
    rw [div_le_iff₀ (by positivity)]
    have : c * lam ^ (j + 1) ≤ c * lam ^ (j + 1) * (j + 1) := by
      have : 0 ≤ c * lam ^ (j + 1) := by positivity
      nlinarith
    linarith [hb (j + 1)]
  have hgeo : Summable fun j : ℕ => c * lam ^ (j + 1) :=
    ((summable_geometric_of_lt_one hl0 hl1).mul_left (c * lam)).congr fun j => by ring
  have hs : Summable W.term := hgeo.of_nonneg_of_le W.term_nonneg hle
  have ht : Tendsto W.EM atTop (𝓝 (∑' j, W.term j)) := by
    have := hs.hasSum.tendsto_sum_nat
    simpa [← EM_eq_sum] using this
  have hsup : (∑' j, W.term j) = ⨆ n, W.EM n :=
    (tendsto_nhds_unique ht (tendsto_atTop_ciSup W.EM_mono
      ⟨∑' j, W.term j, fun _ ⟨n, hn⟩ => hn ▸ by
        rw [EM_eq_sum]; exact hs.sum_le_tsum _ (fun j _ => W.term_nonneg j)⟩))
  refine ⟨hs, ht, hsup, fun n => ?_⟩
  have hsplit := hs.sum_add_tsum_nat_add n
  rw [← EM_eq_sum] at hsplit
  have hs' : Summable fun j => W.term (j + n) := (summable_nat_add_iff n).2 hs
  constructor
  · rw [← hsplit]; simp only [add_sub_cancel_left]
    exact tsum_nonneg fun j => W.term_nonneg _
  · rw [← hsplit, add_sub_cancel_left]
    have hb2 : ∀ j, W.term (j + n) ≤ c * lam ^ (n + 1) / (n + 1) * lam ^ j := fun j => by
      unfold term
      rw [div_le_iff₀ (by positivity)]
      have h1 := hb (j + n + 1)
      have h2 : (n + 1 : ℝ) ≤ ((j + n : ℕ) : ℝ) + 1 := by push_cast; linarith [(j.cast_nonneg : (0:ℝ) ≤ j)]
      have e : c * lam ^ (n + 1) / (n + 1) * lam ^ j * (((j + n : ℕ) : ℝ) + 1) =
          c * lam ^ (j + n + 1) * ((((j + n : ℕ) : ℝ) + 1) / (n + 1)) := by
        field_simp; ring
      rw [e]
      have h3 : 1 ≤ (((j + n : ℕ) : ℝ) + 1) / (n + 1) := by rw [le_div_iff₀ (by positivity)]; linarith
      have h4 : 0 ≤ c * lam ^ (j + n + 1) := by positivity
      exact h1.trans (le_mul_of_one_le_right h4 h3)
    calc ∑' j, W.term (j + n) ≤ ∑' j, c * lam ^ (n + 1) / (n + 1) * lam ^ j :=
          hs'.tsum_le_tsum hb2 ((summable_geometric_of_lt_one hl0 hl1).mul_left _)
      _ = c * lam ^ (n + 1) / ((n + 1) * (1 - lam)) := by
          rw [tsum_mul_left, tsum_geometric_of_lt_one hl0 hl1]
          have : (0:ℝ) < 1 - lam := by linarith
          field_simp

/-- `E(S_k)_+ ≤ λ(θ)^k / θ` for `θ > 0`. -/
theorem ESp_le_mgf {θ : ℝ} (hθ : 0 < θ) (k : ℕ) : W.ESp k ≤ (1 / θ) * W.mgf θ ^ k := by
  rw [← E_exp_S, ← E_mul_const]
  refine W.E_mono k fun z => ?_
  rcases le_total (S z k) 0 with h | h
  · rw [max_eq_right h]; positivity
  · rw [max_eq_left h, one_div, ← div_eq_inv_mul, le_div_iff₀ hθ]
    linarith [Real.add_one_le_exp (θ * S z k)]

/-- Integer valued walks: `E(S_k)_+ ≤ λ(θ)^k / (e^θ - 1)`. -/
theorem ESp_le_mgf_int (hX : ∀ y, ∃ z : ℤ, W.X y = z) {θ : ℝ} (hθ : 0 < θ) (k : ℕ) :
    W.ESp k ≤ (1 / (Real.exp θ - 1)) * W.mgf θ ^ k := by
  have he : 0 < Real.exp θ - 1 := by linarith [Real.add_one_le_exp θ]
  rw [← E_exp_S, ← E_mul_const]
  refine W.E_mono_seq k fun ys => ?_
  choose Xi hXi using hX
  have hint : S (W.seq ys) k = ((∑ i ∈ range k,
      (if h : i < k then Xi (ys ⟨i, h⟩) else 0) : ℤ) : ℝ) := by
    unfold S seq; push_cast
    refine sum_congr rfl fun i _ => ?_
    split_ifs <;> simp [hXi]
  rw [hint]
  generalize (∑ i ∈ range k, (if h : i < k then Xi (ys ⟨i, h⟩) else 0) : ℤ) = s
  rcases le_or_gt s 0 with h | h
  · rw [max_eq_right (by exact_mod_cast h)]; positivity
  · obtain ⟨N, rfl⟩ : ∃ N : ℕ, s = N := ⟨s.toNat, by omega⟩
    push_cast
    rw [max_eq_left (by positivity), one_div, ← div_eq_inv_mul, le_div_iff₀ he]
    have hb := one_add_mul_le_pow (show (-2 : ℝ) ≤ Real.exp θ - 1 by linarith) N
    rw [show 1 + (Real.exp θ - 1) = Real.exp θ by ring, ← Real.exp_nat_mul] at hb
    rw [mul_comm θ]
    nlinarith

/-- Mean of an increment. -/
def mean : ℝ := ∑ y, W.Q y * W.X y

/-- **Existence of θ.** Under negative drift some `θ > 0` has `λ(θ) = E e^{θ X} < 1`. -/
theorem exists_theta (hneg : W.mean < 0) : ∃ θ : ℝ, 0 < θ ∧ W.mgf θ < 1 := by
  set K : ℝ := ∑ y, |W.X y| + 1
  have hK : 0 < K := by positivity
  have hXK : ∀ y, |W.X y| ≤ K := fun y => by
    have := single_le_sum (f := fun y => |W.X y|) (fun y _ => abs_nonneg _) (mem_univ y)
    linarith
  set μ := W.mean
  set θ := min (1 / K) (-μ / (2 * K ^ 2))
  have hK2 : 0 < K ^ 2 := by positivity
  have hθ : 0 < θ := lt_min (by positivity) (div_pos (by linarith) (by positivity))
  refine ⟨θ, hθ, ?_⟩
  have hθK : θ * K ≤ 1 := by
    have := min_le_left (1 / K) (-μ / (2 * K ^ 2))
    calc θ * K ≤ 1 / K * K := mul_le_mul_of_nonneg_right this hK.le
      _ = 1 := by field_simp
  have hθ2 : θ * K ^ 2 ≤ -μ / 2 := by
    have := min_le_right (1 / K) (-μ / (2 * K ^ 2))
    calc θ * K ^ 2 ≤ -μ / (2 * K ^ 2) * K ^ 2 := mul_le_mul_of_nonneg_right this (by positivity)
      _ = -μ / 2 := by field_simp
  have hpt : ∀ y, Real.exp (θ * W.X y) ≤ 1 + θ * W.X y + θ ^ 2 * K ^ 2 := by
    intro y
    have h1 : |θ * W.X y| ≤ 1 := by
      rw [abs_mul, abs_of_pos hθ]
      exact (mul_le_mul_of_nonneg_left (hXK y) hθ.le).trans hθK
    have h2 := Real.abs_exp_sub_one_sub_id_le h1
    have h3 : (θ * W.X y) ^ 2 ≤ θ ^ 2 * K ^ 2 := by
      rw [mul_pow]
      exact mul_le_mul_of_nonneg_left (sq_le_sq' (abs_le.1 (hXK y)).1 (abs_le.1 (hXK y)).2)
        (by positivity)
    linarith [(abs_le.1 h2).2]
  calc W.mgf θ ≤ ∑ y, W.Q y * (1 + θ * W.X y + θ ^ 2 * K ^ 2) :=
        sum_le_sum fun y _ => mul_le_mul_of_nonneg_left (hpt y) (W.Qnn y)
    _ = 1 + θ * μ + θ ^ 2 * K ^ 2 := by
        simp only [mul_add, sum_add_distrib, ← sum_mul, W.Qsum, μ, mean, mul_sum]
        congr 1
        · simp only [mul_one]
          congr 1; exact sum_congr rfl fun y _ => by ring
        · ring
    _ < 1 := by nlinarith

end Law

namespace TwoAction
variable (A : TwoAction)

/-- Shannon entropy of `Q` in bits. -/
def HQ : ℝ := ∑ y, A.Q y * infoMass (A.Q y)

theorem mean_eq : A.law.mean = A.HQ - A.h := by
  show ∑ y, A.Q y * (infoMass (A.Q y) - A.h) = _
  simp only [mul_sub, sum_sub_distrib, ← sum_mul, A.Qsum, one_mul]
  rfl

/-- **Corollary (negative drift).** Under the dyadic assumptions and `H(Q) < h`, with
`ℓ = ∑_{k ≥ 1} E(S_k)_+ / k`: `C_n - n h` is nondecreasing and tends to `ℓ = sup_n (C_n - n h)`;
for every `θ > 0` with `λ = E e^{θ X} < 1`,
`0 ≤ ℓ - (C_n - n h) ≤ λ^{n+1} / (θ (n+1)(1-λ))`; and such a `θ` exists. -/
theorem negative_drift {d : ℕ} (hd : A.Dyadic d) (hH : A.HQ < A.h) :
    Monotone (fun n : ℕ => A.kernel.costBits n - n * A.h) ∧
      Summable A.law.term ∧
      Tendsto (fun n : ℕ => A.kernel.costBits n - n * A.h) atTop (𝓝 (∑' j, A.law.term j)) ∧
      (∑' j, A.law.term j) = ⨆ n : ℕ, (A.kernel.costBits n - n * A.h) ∧
      (∀ θ : ℝ, 0 < θ → A.law.mgf θ < 1 → ∀ n : ℕ,
        0 ≤ (∑' j, A.law.term j) - (A.kernel.costBits n - n * A.h) ∧
        (∑' j, A.law.term j) - (A.kernel.costBits n - n * A.h) ≤
          A.law.mgf θ ^ (n + 1) / (θ * (n + 1) * (1 - A.law.mgf θ))) ∧
      ∃ θ : ℝ, 0 < θ ∧ A.law.mgf θ < 1 := by
  have hc : ∀ n : ℕ, A.kernel.costBits n - n * A.h = A.law.EM n := fun n => by
    rw [A.cost_eq hd]; ring
  simp only [hc]
  have hneg : A.law.mean < 0 := by rw [mean_eq]; linarith
  obtain ⟨θ0, hθ0, hl0⟩ := A.law.exists_theta hneg
  have hmgf0 : ∀ θ, 0 ≤ A.law.mgf θ := fun θ =>
    sum_nonneg fun y _ => mul_nonneg (A.law.Qnn y) (Real.exp_pos _).le
  obtain ⟨hs, ht, hsup, -⟩ := A.law.tail_bound (by positivity : (0:ℝ) ≤ 1 / θ0) (hmgf0 θ0) hl0
    (A.law.ESp_le_mgf hθ0)
  refine ⟨A.law.EM_mono, hs, ht, hsup, fun θ hθ hl n => ?_, θ0, hθ0, hl0⟩
  obtain ⟨-, -, -, hb⟩ := A.law.tail_bound (by positivity : (0:ℝ) ≤ 1 / θ) (hmgf0 θ) hl
    (A.law.ESp_le_mgf hθ)
  refine ⟨(hb n).1, (hb n).2.trans (le_of_eq ?_)⟩
  field_simp

end TwoAction
end CausalSpectrum.Walk
