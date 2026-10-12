/-
One pair of block absorption, assembled: the product block of `p` samples of `K_{j₀}`
coupled (by the refined interval coupling) with the exact finite seed of
`causal_truncation` for the subfamily at horizon `q`. Its entropy exceeds `p H(K_{j₀})`
by at most `exc p q`.
-/
import CausalSeed.GapInterleave
import CausalSeed.GapPair
import CausalSeed.GapTail

noncomputable section
open Classical Finset
open scoped ENNReal

namespace CausalSpectrum.Kernel
open Completion Gap

variable {κ : Kernel} (j₀ : Fin κ.nA) (h2 : 2 ≤ κ.nA)

/-- The exact finite subfamily seed at horizon `q`. -/
def atomsQ (q : ℕ) : List (Atom (trunc (subK j₀ h2).toITree q [])) :=
  (causal_truncation (trunc (subK j₀ h2).toITree q [])).choose

theorem atomsQ_spec (q : ℕ) :
    (∀ a ∈ atomsQ j₀ h2 q, 0 < a.1) ∧ totalWeight (atomsQ j₀ h2 q) = 1 ∧
    (∀ (π : Policy (trunc (subK j₀ h2).toITree q [])) (ℓ : Leaf (trunc (subK j₀ h2).toITree q [])),
        transcriptWeight (atomsQ j₀ h2 q) π ℓ = if CompatiblePolicy ℓ π then leafMass ℓ else 0) ∧
    (∀ t s : ℝ, 0 ≤ s → seedTail (atomsQ j₀ h2 q) (t + s) ≤
        (1 - Fstar (trunc (subK j₀ h2).toITree q []) t) + (2 : ℝ) ^ (-s)) := by
  obtain ⟨-, hpos, htot, hex, htail, -⟩ := (causal_truncation (trunc (subK j₀ h2).toITree q [])).choose_spec
  exact ⟨hpos, htot, hex, htail⟩

/-- Retention threshold. -/
def thB (δ : ℝ) (q : ℕ) : ℝ := (2:ℝ) ^ (-(q * (subK j₀ h2).hmax + 2 * δ * q))

/-- Heavy threshold for the product block. -/
def thA (δx : ℝ) (p : ℕ) : ℝ := (2:ℝ) ^ (-(p * (Hb (κ.K j₀) - δx)))

/-- The product block as a law on `ℕ`. -/
def aN (p : ℕ) (k : ℕ) : ℝ :=
  if h : k < Fintype.card (Fin p → Fin (κ.nY j₀)) then
    prodW (κ.K j₀) ((Fintype.equivFin (Fin p → Fin (κ.nY j₀))).symm ⟨k, h⟩) else 0

variable {j₀}

theorem sum_equivFin {p : ℕ} (F : ℕ → ℝ) :
    ∑ x : Fin p → Fin (κ.nY j₀), F (Fintype.equivFin _ x) =
      ∑ k ∈ range (Fintype.card (Fin p → Fin (κ.nY j₀))), F k := by
  rw [← Fin.sum_univ_eq_sum_range]
  exact Equiv.sum_comp (Fintype.equivFin _) (fun k => F k)

theorem aN_equiv {p : ℕ} (x : Fin p → Fin (κ.nY j₀)) :
    aN j₀ p (Fintype.equivFin _ x) = prodW (κ.K j₀) x := by
  unfold aN; rw [dif_pos (Fintype.equivFin _ x).isLt]; simp

theorem aN_nonneg (p k : ℕ) : 0 ≤ aN j₀ p k := by
  unfold aN; split_ifs
  · exact (prodW_pos (κ.Kpos j₀) _).le
  · exact le_rfl

theorem cum_aN (p : ℕ) : cum (aN j₀ p) (Fintype.card (Fin p → Fin (κ.nY j₀))) = 1 := by
  unfold cum
  rw [← sum_equivFin]
  simp_rw [aN_equiv]
  exact sum_prodW (κ.Ksum j₀) p

variable (j₀)

theorem cum_atomsQ (q : ℕ) : cum (atomWeight (atomsQ j₀ h2 q)) (atomsQ j₀ h2 q).length = 1 := by
  unfold cum
  rw [Completion.sum_range_atomWeight (fun x => x)]
  exact (atomsQ_spec j₀ h2 q).2.1

/-- The pair component. -/
def mkComp (δ : ℝ) (p q : ℕ) : Comp j₀ h2 p q where
  Ω := (Fin p → Fin (κ.nY j₀)) × Fin (atomsQ j₀ h2 q).length
  w o := piC (aN j₀ p) (atomWeight (atomsQ j₀ h2 q)) (atomsQ j₀ h2 q).length (thB j₀ h2 δ q)
    (Fintype.equivFin _ o.1) o.2
  xp o := o.1
  bs o := (atomSeed (atomsQ_spec j₀ h2 q).1 (atomsQ_spec j₀ h2 q).2.1).strategy o.2
  nonneg o := piC_nonneg (atomWeight_nonneg' (atomsQ_spec j₀ h2 q).1) _ _
  total := by
    rw [Fintype.sum_prod_type]
    have := fun x : Fin p → Fin (κ.nY j₀) => (Fin.sum_univ_eq_sum_range (fun i =>
      piC (aN j₀ p) (atomWeight (atomsQ j₀ h2 q)) (atomsQ j₀ h2 q).length (thB j₀ h2 δ q)
        (Fintype.equivFin _ x) i) (atomsQ j₀ h2 q).length)
    simp_rw [this]
    simp_rw [piC_sum_right (aN_nonneg p) (atomWeight_nonneg' (atomsQ_spec j₀ h2 q).1)
      ((cum_aN p).trans (cum_atomsQ j₀ h2 q).symm) (Fin.isLt _), aN_equiv]
    exact sum_prodW (κ.Ksum j₀) p
  mX E := by
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun x _ => ?_
    by_cases hE : E x
    swap
    · simp [hE]
    simp only [hE, if_true, mul_one]
    rw [Fin.sum_univ_eq_sum_range (fun i =>
      piC (aN j₀ p) (atomWeight (atomsQ j₀ h2 q)) (atomsQ j₀ h2 q).length (thB j₀ h2 δ q)
        (Fintype.equivFin _ x) i) (atomsQ j₀ h2 q).length,
      piC_sum_right (aN_nonneg p) (atomWeight_nonneg' (atomsQ_spec j₀ h2 q).1)
      ((cum_aN p).trans (cum_atomsQ j₀ h2 q).symm) (Fin.isLt _), aN_equiv]
  mB L hL := by
    rw [Fintype.sum_prod_type, sum_comm]
    simp_rw [← Finset.sum_mul]
    have hS := atomSeed_exactTo (atomsQ_spec j₀ h2 q).1 (atomsQ_spec j₀ h2 q).2.1
      (atomsQ_spec j₀ h2 q).2.2.1 L hL
    rw [← hS]
    unfold CountableSeed.hit
    rw [tsum_eq_sum (s := range (atomsQ j₀ h2 q).length) (fun i hi => by
      simp [atomSeed, atomWeight_ge _ (not_lt.1 (by simpa using hi))]),
      ← Fin.sum_univ_eq_sum_range (fun i => (atomSeed (atomsQ_spec j₀ h2 q).1
        (atomsQ_spec j₀ h2 q).2.1).weight i * indAgree _ ((atomSeed (atomsQ_spec j₀ h2 q).1
        (atomsQ_spec j₀ h2 q).2.1).strategy i) L)]
    refine sum_congr rfl fun i _ => ?_
    congr 1
    rw [sum_equivFin (fun k => piC (aN j₀ p) (atomWeight (atomsQ j₀ h2 q))
      (atomsQ j₀ h2 q).length (thB j₀ h2 δ q) k i)]
    rw [piC_sum_left (aN_nonneg p) (atomWeight_nonneg' (atomsQ_spec j₀ h2 q).1)
      ((cum_aN p).trans (cum_atomsQ j₀ h2 q).symm) i.isLt]
    rfl

/-- Retention exponent `u = q h' + 2 δ q`. -/
def uB (δ : ℝ) (q : ℕ) : ℝ := q * (subK j₀ h2).hmax + 2 * δ * q

/-- The Hoeffding constant of `K_{j₀}`. -/
def Mx : ℝ := (fam1 (κ.hY j₀) (κ.Kpos j₀) (κ.Ksum j₀)).M

/-- Excess entropy of one pair over `p H(K_{j₀})` (nats). -/
def exc (δ δx : ℝ) (p q : ℕ) : ℝ :=
  (Real.exp (-(p * δx ^ 2 / (2 * (Mx j₀ ^ 2 + 1)))) +
      ((2:ℝ) ^ uB j₀ h2 δ q + 1) * thA j₀ δx p) * Real.log ((2:ℝ) ^ uB j₀ h2 δ q + 1) +
    Tb (subK j₀ h2) δ q

/-- **Pair entropy.** -/
theorem mkComp_entropy {δ δx : ℝ} (hδ : 0 < δ) (hδx : 0 ≤ δx) (p q : ℕ) :
    ∑ o, Real.negMulLog ((mkComp j₀ h2 δ p q).w o) ≤
      p * ∑ y, Real.negMulLog (κ.K j₀ y) + exc j₀ h2 δ δx p q := by
  set atoms := atomsQ j₀ h2 q
  obtain ⟨hpos, htot, hex, htail⟩ := atomsQ_spec j₀ h2 q
  have hb := atomWeight_nonneg' hpos
  have he := (cum_aN (j₀ := j₀) p).trans (cum_atomsQ j₀ h2 q).symm
  have hL : ∑ o, Real.negMulLog ((mkComp j₀ h2 δ p q).w o) =
      ∑ k ∈ range (Fintype.card (Fin p → Fin (κ.nY j₀))), ∑ i ∈ range atoms.length,
        Real.negMulLog (piC (aN j₀ p) (atomWeight atoms) atoms.length (thB j₀ h2 δ q) k i) := by
    show ∑ o : (Fin p → Fin (κ.nY j₀)) × Fin atoms.length, Real.negMulLog (piC (aN j₀ p)
      (atomWeight atoms) atoms.length (thB j₀ h2 δ q) (Fintype.equivFin _ o.1) o.2) = _
    rw [Fintype.sum_prod_type]
    rw [← sum_equivFin (fun k => ∑ i ∈ range atoms.length,
        Real.negMulLog (piC (aN j₀ p) (atomWeight atoms) atoms.length (thB j₀ h2 δ q) k i))]
    refine sum_congr rfl fun x _ => ?_
    exact Fin.sum_univ_eq_sum_range (fun i => Real.negMulLog
      (piC (aN j₀ p) (atomWeight atoms) atoms.length (thB j₀ h2 δ q) (Fintype.equivFin _ x) i)) _
  rw [hL]
  have hθ : 0 ≤ thA j₀ δx p := by unfold thA; positivity
  refine (piC_entropy_le' (aN_nonneg p) hb he (cum_atomsQ j₀ h2 q) hθ).trans ?_
  -- the four pieces
  have h1 : ∑ k ∈ range (Fintype.card (Fin p → Fin (κ.nY j₀))), Real.negMulLog (aN j₀ p k) =
      p * ∑ y, Real.negMulLog (κ.K j₀ y) := by
    rw [← sum_equivFin]; simp_rw [aN_equiv]; exact entropy_prodW (κ.Kpos j₀) (κ.Ksum j₀) p
  have h2' : (∑ k ∈ range (Fintype.card (Fin p → Fin (κ.nY j₀))),
      if thA j₀ δx p < aN j₀ p k then aN j₀ p k else 0) ≤
        Real.exp (-(p * δx ^ 2 / (2 * (Mx j₀ ^ 2 + 1)))) := by
    rw [← sum_equivFin (fun k => if thA j₀ δx p < aN j₀ p k then aN j₀ p k else 0)]
    simp_rw [aN_equiv]
    refine le_trans (le_of_eq (sum_congr rfl fun x _ => ?_))
      (heavy_mass_le (κ.hY j₀) (κ.Kpos j₀) (κ.Ksum j₀) p hδx)
    have hp := prodW_pos (κ.Kpos j₀) x
    have : thA j₀ δx p < prodW (κ.K j₀) x ↔ infoMass (prodW (κ.K j₀) x) < p * (Hb (κ.K j₀) - δx) := by
      unfold thA infoMass
      rw [← Real.rpow_logb (by norm_num : (0:ℝ) < 2) (by norm_num) hp,
        Real.rpow_lt_rpow_left_iff (by norm_num), Real.logb_rpow (by norm_num) (by norm_num)]
      constructor <;> intro h <;> linarith
    by_cases hc : thA j₀ δx p < prodW (κ.K j₀) x
    · rw [if_pos hc, if_pos (this.1 hc), mul_one]
    · rw [if_neg hc, if_neg (fun h => hc (this.2 h)), mul_zero]
  have hcnt : (((range atoms.length).filter fun i => thB j₀ h2 δ q ≤ atomWeight atoms i).card : ℝ)
      ≤ (2:ℝ) ^ uB j₀ h2 δ q := by
    have hpos' : 0 < thB j₀ h2 δ q := by unfold thB; positivity
    refine (card_heavy_le hb (cum_atomsQ j₀ h2 q) hpos').trans (le_of_eq ?_)
    unfold thB uB; rw [Real.rpow_neg (by norm_num), one_div, inv_inv]
  have h4 := tail_entropy_le (subK j₀ h2) hδ q atoms hpos htail
  set k := ((range atoms.length).filter fun i => thB j₀ h2 δ q ≤ atomWeight atoms i).card
  have hk1 : (1:ℝ) ≤ (k:ℝ) + 1 := by linarith [(Nat.cast_nonneg k : (0:ℝ) ≤ k)]
  have hlog : Real.log ((k:ℝ) + 1) ≤ Real.log ((2:ℝ) ^ uB j₀ h2 δ q + 1) :=
    Real.log_le_log (by linarith) (by linarith)
  have hl0 : 0 ≤ Real.log ((k:ℝ) + 1) := Real.log_nonneg hk1
  have hH0 : 0 ≤ ∑ k ∈ range (Fintype.card (Fin p → Fin (κ.nY j₀))),
      (if thA j₀ δx p < aN j₀ p k then aN j₀ p k else 0) :=
    sum_nonneg fun k _ => by split_ifs <;> simp [aN_nonneg p k]
  unfold exc
  rw [h1]
  have hA : ((∑ k ∈ range (Fintype.card (Fin p → Fin (κ.nY j₀))),
      if thA j₀ δx p < aN j₀ p k then aN j₀ p k else 0) + ((k:ℝ) + 1) * thA j₀ δx p) *
        Real.log ((k:ℝ) + 1) ≤
      (Real.exp (-(p * δx ^ 2 / (2 * (Mx j₀ ^ 2 + 1)))) +
        ((2:ℝ) ^ uB j₀ h2 δ q + 1) * thA j₀ δx p) * Real.log ((2:ℝ) ^ uB j₀ h2 δ q + 1) := by
    apply mul_le_mul _ hlog hl0 (by positivity)
    have : ((k:ℝ) + 1) * thA j₀ δx p ≤ ((2:ℝ) ^ uB j₀ h2 δ q + 1) * thA j₀ δx p :=
      mul_le_mul_of_nonneg_right (by linarith) hθ
    exact add_le_add (by simpa [Mx] using h2') this
  have h4' : ∑ i ∈ range atoms.length, (if atomWeight atoms i < thB j₀ h2 δ q then
      Real.negMulLog (atomWeight atoms i) else 0) ≤ Tb (subK j₀ h2) δ q := h4
  linarith

end CausalSpectrum.Kernel
