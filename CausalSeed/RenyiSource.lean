/-
Rényi spectrum, stage 3: ordinary sources exact at all horizons.

An *ordinary exact source* on a locally finite controlled tree `ι` is a countable
law `w` together with, for every horizon `n`, a deterministic readout of a joint
transcript (one transcript per horizon-`n` policy) whose `π`-marginal is the
true transcript law for every policy `π`.  Readouts at different horizons, and
for different policies, need not be consistent with each other: this is the
ordinary (possibly history-inconsistent) class of the note.
Every exact causal seed is such a source (`ofSeed`).  Each horizon-`n` readout
pushes `w` to a `Coupling` of the truncation, so the finite lower bound
`R_α(Z_n) ≤ H_α(Γ)` and data processing give `R_α(Z_n) ≤ H_α(U)`.
-/
import CausalSeed.RenyiCountable
import CausalSeed.SeedDataProcessing
import CausalSeed.EnvelopeBridge
import Mathlib.Analysis.Normed.Group.Tannery

noncomputable section
open Classical Finset Filter
open scoped ENNReal Topology
namespace CausalSpectrum.RenyiInf
open CausalSpectrum.Completion

structure OrdSource (ι : ITree) where
  w : ℕ → ℝ
  law : IsLaw w
  read : (n : ℕ) → ℕ → CausalSpectrum.Assignment (trunc ι n [])
  marginal : ∀ (n : ℕ) (π : Policy (trunc ι n [])) (ℓ : Leaf (trunc ι n [])),
    CompatiblePolicy ℓ π → ∑' i, (if ((read n i) π).1 = ℓ then w i else 0) = leafMass ℓ

namespace OrdSource
variable {ι : ITree}

/-- The horizon-`n` coupling of an ordinary source. -/
def coupling (U : OrdSource ι) (n : ℕ) : Coupling (trunc ι n []) where
  mass := push U.w (U.read n)
  nonneg := push_nonneg U.law _
  total := push_total U.law _
  marginal := by
    intro π ℓ hc
    rw [push_event U.law (U.read n) (fun b => (b π).1 = ℓ)]
    exact U.marginal n π ℓ hc

theorem push_le_one (U : OrdSource ι) (n : ℕ) (b) : push U.w (U.read n) b ≤ 1 := by
  rw [← push_total U.law (U.read n)]
  exact Finset.single_le_sum (f := fun b => push U.w (U.read n) b)
    (fun b _ => push_nonneg U.law _ b) (Finset.mem_univ b)

/-- Lower bound at one horizon, `α ≠ 1`: `R_α(Z_n) ≤ H_α(U)`. -/
theorem zRenyi_le (U : OrdSource ι) (n : ℕ) {α : ℝ} (hα : 0 < α) (hα1 : α ≠ 1) :
    ENNReal.ofReal (Renyi.zRenyi (trunc ι n []) α) ≤ H α U.w := by
  have hz := Renyi.coupRenyi_ge (trunc ι n []) hα hα1 (U.coupling n)
  unfold Renyi.coupRenyi at hz
  simp only [coupling] at hz
  rcases lt_or_gt_of_ne hα1 with hlt | hgt
  · unfold H renyiNe
    rw [if_neg hα1]
    split_ifs with htop
    · exact le_top
    have hdp := dp_le U.law (U.read n) hα hlt.le
    have hsum1 : 1 ≤ ∑ b, push U.w (U.read n) b ^ α := by
      rw [← push_total U.law (U.read n)]
      refine Finset.sum_le_sum fun b _ => ?_
      rcases (push_nonneg U.law (U.read n) b).eq_or_lt with h0 | hp
      · rw [← h0, Real.zero_rpow hα.ne']
      · simpa using Real.rpow_le_rpow_of_exponent_ge hp (U.push_le_one n b) hlt.le
    have hle : ∑ b, push U.w (U.read n) b ^ α ≤ (mom α U.w).toReal := by
      rw [← ENNReal.ofReal_sum_of_nonneg (fun b _ => Real.rpow_nonneg (push_nonneg U.law _ b) _)]
        at hdp
      have := ENNReal.toReal_mono htop hdp
      rwa [ENNReal.toReal_ofReal (Finset.sum_nonneg fun b _ =>
        Real.rpow_nonneg (push_nonneg U.law _ b) _)] at this
    apply ENNReal.ofReal_le_ofReal
    refine hz.trans (div_le_div_of_nonneg_right ?_ (by linarith))
    exact Real.logb_le_logb_of_le (by norm_num) (by linarith) hle
  · rw [H_of_gt U.law hgt]
    apply ENNReal.ofReal_le_ofReal
    refine hz.trans ?_
    unfold hreal
    have hdp := (dp_ge U.law (U.read n) hgt.le).2
    exact div_le_div_of_nonpos_of_le (by linarith)
      (Real.logb_le_logb_of_le (by norm_num) (tsum_rpow_pos U.law hgt.le) hdp)

/-- A dummy strategy, to view the law of `U` as a `Seed`. -/
def dummy (ι : ITree) : IStrategy ι := fun p => ⟨0, ι.hY p.1 p.2⟩

def asSeed (U : OrdSource ι) : Seed ι := ⟨U.w, U.law.nonneg, U.law.sum, fun _ => dummy ι⟩

/-- Lower bound at one horizon, `α = 1`: `L_n ≤ H(U)` (bits). -/
theorem envelope_le (U : OrdSource ι) (n : ℕ) :
    ENNReal.ofReal (envelopeMean (trunc ι n [])) ≤ H 1 U.w := by
  have h1 := entropy_ge_envelope (U.coupling n)
  have h2 := Seed.push_entropy_le U.asSeed (U.read n)
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  unfold H shannonBits
  rw [if_pos rfl, ENNReal.le_div_iff_mul_le (Or.inl (ENNReal.ofReal_pos.mpr hl).ne')
    (Or.inl ENNReal.ofReal_ne_top)]
  have he : Real.log 2 * (U.coupling n).entropy =
      ∑ b, Real.negMulLog (push U.w (U.read n) b) := by
    simp only [Coupling.entropy, pmfEntropy, Finset.mul_sum, log_two_mul_entTerm, coupling]
  calc ENNReal.ofReal (envelopeMean (trunc ι n [])) * ENNReal.ofReal (Real.log 2)
      ≤ ENNReal.ofReal ((U.coupling n).entropy) * ENNReal.ofReal (Real.log 2) := by
        gcongr
    _ = ENNReal.ofReal (Real.log 2 * (U.coupling n).entropy) := by
        rw [mul_comm (Real.log 2), ENNReal.ofReal_mul' hl.le]
    _ = ∑ b, ENNReal.ofReal (Real.negMulLog (push U.w (U.read n) b)) := by
        rw [he, ENNReal.ofReal_sum_of_nonneg fun b _ =>
          Real.negMulLog_nonneg (push_nonneg U.law _ b) (U.push_le_one n b)]
    _ ≤ _ := h2

/-! ### Tails -/

/-- `P(I_U > s)`. -/
def tailU (w : ℕ → ℝ) (s : ℝ) : ℝ := ∑' i, if s < infoMass (w i) then w i else 0

theorem one_sub_Fstar_le (U : OrdSource ι) (n : ℕ) (s : ℝ) :
    1 - Fstar (trunc ι n []) s ≤ tailU U.w s := by
  have h := Renyi.coup_tail_ge (trunc ι n []) (U.coupling n) s
  have h' : 1 - Fstar (trunc ι n []) s ≤
      ∑ b, if s < infoMass (push U.w (U.read n) b) then push U.w (U.read n) b else 0 := by
    refine h.trans_eq (Finset.sum_congr rfl fun b _ => ?_)
    exact ite_congr rfl (fun _ => rfl) (fun _ => rfl)
  rw [push_event U.law (U.read n) (fun b => s < infoMass (push U.w (U.read n) b))] at h'
  replace h := h'
  refine h.trans (Summable.tsum_le_tsum (fun i => ?_) ?_ ?_)
  · by_cases hw : U.w i = 0
    · simp [hw]
    have hp : 0 < U.w i := lt_of_le_of_ne (U.law.nonneg i) (Ne.symm hw)
    split_ifs with h1 h2
    · exact le_rfl
    · exact absurd (h1.trans_le (infoMass_anti hp (hp.trans_le (weight_le_push U.law _ i))
        (weight_le_push U.law _ i))) h2
    · exact hp.le
    · exact le_rfl
  · exact Summable.of_nonneg_of_le (fun i => by split_ifs <;> simp [U.law.nonneg])
      (fun i => by split_ifs <;> simp [U.law.nonneg]) U.law.sum.summable
  · exact Summable.of_nonneg_of_le (fun i => by split_ifs <;> simp [U.law.nonneg])
      (fun i => by split_ifs <;> simp [U.law.nonneg]) U.law.sum.summable

theorem tailU_tendsto {w : ℕ → ℝ} (hw : IsLaw w) : Tendsto (tailU w) atTop (𝓝 0) := by
  have h := tendsto_tsum_of_dominated_convergence (𝓕 := atTop)
    (f := fun s i => if s < infoMass (w i) then w i else 0) (g := fun _ => (0:ℝ))
    hw.sum.summable (fun i => ?_) (Eventually.of_forall fun s i => ?_)
  · unfold tailU; convert h; simp
  · apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop (infoMass (w i))] with s hs
    simp [not_lt.mpr hs]
  · split_ifs <;> simp [abs_of_nonneg (hw.nonneg i), hw.nonneg i]

/-! ### Causal seeds are ordinary sources -/

def ofSeed (G : CountableSeed ι) (hG : G.Exact) : OrdSource ι where
  w := G.weight
  law := ⟨G.nonneg, G.mass⟩
  read n i := CountableSeed.assign ι n (G.strategy i)
  marginal := by
    intro n π ℓ hc
    have hm := (G.coupling n (hG n)).marginal π ℓ hc
    have hw : IsLaw G.weight := ⟨G.nonneg, G.mass⟩
    have he := push_event hw (fun i => CountableSeed.assign ι n (G.strategy i))
      (fun b => (b π).1 = ℓ)
    rw [← he, ← hm]
    rfl

@[simp] theorem ofSeed_w (G : CountableSeed ι) (hG : G.Exact) : (ofSeed G hG).w = G.weight := rfl

#print axioms zRenyi_le
#print axioms envelope_le
#print axioms one_sub_Fstar_le

end OrdSource
end CausalSpectrum.RenyiInf
