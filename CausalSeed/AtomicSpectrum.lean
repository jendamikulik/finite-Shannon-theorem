/-
Atomic capacity as the escape-free mass of the information envelope
(atomic_capacity.tex, §"Information spectrum and entropy"):

  `F_∞(t) = inf_n F_n(t)`,  `F_n = Fstar (trunc ι n [])`  (min over policies of the
  information CDF `P_{n,π}{-log₂ P_{n,π}(X) ≤ t}`),

  `atomQ ι = lim_{t→∞} F_∞(t)`.

The proof is the two per-law inequalities `F_P(t) ≤ A_{⌊2^t⌋}(P)` and
`A_K(P) ≤ F_P(t) + K 2^{-t}`, with infima over all finite-policy laws.
-/
import CausalSeed.Atomic
import CausalSeed.Entropy

noncomputable section
open Classical Finset Filter
open scoped Topology
namespace CausalSpectrum

/-- `F_∞(t) = inf_n F_n(t)`. -/
def FInf (ι : ITree) (t : ℝ) : ℝ := ⨅ n : ℕ, Fstar (trunc ι n []) t

theorem FInf_bdd (ι : ITree) (t : ℝ) :
    BddBelow (Set.range fun n : ℕ => Fstar (trunc ι n []) t) :=
  ⟨0, by rintro _ ⟨n, rfl⟩; exact Fstar_nonneg _ t⟩

theorem FInf_le (ι : ITree) (t : ℝ) (n : ℕ) : FInf ι t ≤ Fstar (trunc ι n []) t :=
  ciInf_le (FInf_bdd ι t) n

theorem FInf_mono (ι : ITree) : Monotone (FInf ι) := fun s t hst =>
  le_ciInf fun n => (FInf_le ι s n).trans (Fstar_mono _ hst)

theorem info_le_iff {m t : ℝ} (hm : 0 < m) : infoMass m ≤ t ↔ (2:ℝ) ^ (-t) ≤ m := by
  have := weight_lt_dyadic_iff (t := t) hm
  constructor
  · intro h; by_contra h'; push_neg at h'; linarith [this.mp h']
  · intro h; by_contra h'; push_neg at h'; linarith [this.mpr h']

theorem policyCDF_eq {T : Tree} (π : Policy T) (t : ℝ) :
    policyCDF T π t = ∑ ℓ ∈ (univ.filter fun ℓ : Leaf T => CompatiblePolicy ℓ π),
      (if infoMass (leafMass ℓ) ≤ t then leafMass ℓ else 0) := by
  unfold policyCDF; rw [policySum_eq_compatible]

theorem compat_sum {T : Tree} (π : Policy T) :
    ∑ ℓ ∈ (univ.filter fun ℓ : Leaf T => CompatiblePolicy ℓ π), leafMass ℓ = 1 := by
  rw [← policySum_eq_compatible]; exact policySum_leafMass π

/-- `F_P(t) ≤ A_{⌊2^t⌋}(P)`. -/
theorem policyCDF_le_top {T : Tree} (π : Policy T) (t : ℝ) :
    policyCDF T π t ≤ topMass T π ⌊(2:ℝ) ^ t⌋₊ := by
  set C := univ.filter fun ℓ : Leaf T => CompatiblePolicy ℓ π
  set D := C.filter fun ℓ => infoMass (leafMass ℓ) ≤ t
  have hcdf : policyCDF T π t = ∑ ℓ ∈ D, leafMass ℓ := by
    rw [policyCDF_eq, Finset.sum_filter]
    simp only [D, C, Finset.sum_filter]
  have h2 : 0 < (2:ℝ) ^ (-t) := Real.rpow_pos_of_pos (by norm_num) _
  have hcard : (D.card : ℝ) * (2:ℝ) ^ (-t) ≤ 1 := by
    calc (D.card : ℝ) * (2:ℝ) ^ (-t) = ∑ ℓ ∈ D, (2:ℝ) ^ (-t) := by simp
      _ ≤ ∑ ℓ ∈ D, leafMass ℓ := Finset.sum_le_sum fun ℓ hℓ =>
          (info_le_iff (leafMass_pos ℓ)).mp (Finset.mem_filter.mp hℓ).2
      _ ≤ ∑ ℓ ∈ C, leafMass ℓ := Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.filter_subset _ _) fun ℓ _ _ => (leafMass_pos ℓ).le
      _ = 1 := compat_sum π
  have hD : D.card ≤ ⌊(2:ℝ) ^ t⌋₊ := by
    apply Nat.le_floor
    have : (2:ℝ) ^ (-t) * (2:ℝ) ^ t = 1 := by
      rw [← Real.rpow_add (by norm_num)]; simp
    nlinarith [Real.rpow_pos_of_pos (show (0:ℝ) < 2 by norm_num) t]
  rw [hcdf]
  exact topMass_le_of_set π _ hD fun ℓ hℓ =>
    (Finset.mem_filter.mp (Finset.mem_filter.mp hℓ).1).2

/-- `A_K(P) ≤ F_P(t) + K 2^{-t}`. -/
theorem top_le_policyCDF {T : Tree} (π : Policy T) (K : ℕ) (t : ℝ) :
    topMass T π K ≤ policyCDF T π t + K * (2:ℝ) ^ (-t) := by
  set D := topSet T π K
  obtain ⟨hcard, hc⟩ := card_topSet T π K
  have split : ∀ ℓ ∈ D, leafMass ℓ ≤
      (if infoMass (leafMass ℓ) ≤ t then leafMass ℓ else 0) + (2:ℝ) ^ (-t) := by
    intro ℓ _
    have h2 : 0 < (2:ℝ) ^ (-t) := Real.rpow_pos_of_pos (by norm_num) _
    split_ifs with h
    · linarith
    · have := (weight_lt_dyadic_iff (t := t) (leafMass_pos ℓ)).mpr (not_le.mp h)
      linarith
  have h1 : ∑ ℓ ∈ D, (if infoMass (leafMass ℓ) ≤ t then leafMass ℓ else 0) ≤ policyCDF T π t := by
    rw [policyCDF_eq]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro ℓ hℓ; simp [hc ℓ hℓ]
    · intro ℓ _ _; split_ifs <;> simp [(leafMass_pos ℓ).le]
  have h3 : ∑ ℓ ∈ D, (2:ℝ) ^ (-t) ≤ K * (2:ℝ) ^ (-t) := by
    rw [Finset.sum_const, nsmul_eq_mul]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard)
      (Real.rpow_pos_of_pos (by norm_num) _).le
  calc topMass T π K = ∑ ℓ ∈ D, leafMass ℓ := rfl
    _ ≤ ∑ ℓ ∈ D, ((if infoMass (leafMass ℓ) ≤ t then leafMass ℓ else 0) + (2:ℝ) ^ (-t)) :=
        Finset.sum_le_sum split
    _ ≤ _ := by rw [Finset.sum_add_distrib]; linarith

theorem FInf_le_atomA (ι : ITree) (t : ℝ) : FInf ι t ≤ atomA ι ⌊(2:ℝ) ^ t⌋₊ :=
  le_csInf (atomA_nonempty ι _) fun x ⟨n, π, hx⟩ => by
    rw [hx]
    exact (FInf_le ι t n).trans ((Fstar_le _ t π).trans (policyCDF_le_top π t))

theorem FInf_le_atomQ (ι : ITree) (t : ℝ) : FInf ι t ≤ atomQ ι :=
  (FInf_le_atomA ι t).trans (atomA_le_atomQ ι _)

theorem atomA_le_FInf (ι : ITree) (K : ℕ) (t : ℝ) :
    atomA ι K - K * (2:ℝ) ^ (-t) ≤ FInf ι t := by
  refine le_ciInf fun n => ?_
  have h := (atomA_le_top ι K n (envelopePolicy (trunc ι n []) t)).trans
    (top_le_policyCDF (envelopePolicy (trunc ι n []) t) K t)
  have : Fstar (trunc ι n []) t = policyCDF (trunc ι n []) (envelopePolicy (trunc ι n []) t) t := rfl
  linarith

/-- **`atomQ = lim_{t→∞} F_∞(t)`** (atomic_capacity.tex, boxed identity of §4). -/
theorem atomQ_eq_lim_FInf (ι : ITree) : Tendsto (FInf ι) atTop (𝓝 (atomQ ι)) := by
  rw [tendsto_order]
  refine ⟨fun b hb => ?_, fun b hb => Eventually.of_forall fun t => (FInf_le_atomQ ι t).trans_lt hb⟩
  obtain ⟨_, ⟨K, rfl⟩, hK⟩ := exists_lt_of_lt_csSup (Set.range_nonempty (atomA ι)) hb
  have hpow : Tendsto (fun t : ℝ => (K:ℝ) * (2:ℝ) ^ (-t)) atTop (𝓝 0) := by
    have h : Tendsto (fun s : ℝ => (2:ℝ) ^ (-s)) atTop (𝓝 0) := by
      have := tendsto_rpow_neg_atTop (y := 1) one_pos
      have e : ∀ s : ℝ, (2:ℝ) ^ (-s) = ((2:ℝ) ^ s) ^ (-(1:ℝ)) := fun s => by
        rw [← Real.rpow_mul (by norm_num)]; ring_nf
      simp_rw [e]
      exact this.comp (tendsto_rpow_atTop_of_base_gt_one 2 (by norm_num))
    simpa using h.const_mul (K:ℝ)
  filter_upwards [hpow.eventually (gt_mem_nhds (show 0 < atomA ι K - b by linarith))] with t ht
  linarith [atomA_le_FInf ι K t]

/-- The supremum form: `atomQ = sup_t F_∞(t)`. -/
theorem atomQ_eq_iSup_FInf (ι : ITree) : atomQ ι = ⨆ t : ℝ, FInf ι t :=
  (tendsto_nhds_unique (atomQ_eq_lim_FInf ι)
    (tendsto_atTop_ciSup (FInf_mono ι) ⟨atomQ ι, by rintro _ ⟨t, rfl⟩; exact FInf_le_atomQ ι t⟩))

#print axioms policyCDF_le_top
#print axioms top_le_policyCDF
#print axioms atomQ_eq_lim_FInf
#print axioms atomQ_eq_iSup_FInf

end CausalSpectrum
