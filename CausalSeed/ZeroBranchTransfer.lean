/-
Infinite-horizon consequences for trees with zero branches.

The positive-tree theorems (projective entropy identity and attainment, the `L∞` sandwich,
atomic capacity and its spectral formula, the simultaneous Rényi seed) transfer to a nonnegative
history-dependent tree `T` with every zero branch retained, through the seed correspondence of
`ZeroBranchSeed` and the spectrum equality of `ZeroBranchSpectrum`.
-/
import CausalSeed.ZeroBranchSpectrum
import CausalSeed.InfiniteEnvelope
import CausalSeed.AtomicCapacity
import CausalSeed.AtomicSpectrum
import CausalSeed.RenyiLimitMeasure

noncomputable section
open Classical Finset MeasureTheory Filter
open scoped ENNReal Topology

namespace CausalSpectrum.ZeroBranch
open Completion

namespace NNTree
variable (T : NNTree)

/-! ### Spectral quantities of `T` -/

/-- `L∞(T) = sup_n L(T_n)` (bits), computed on the trees with all branches retained. -/
def Linf : ℝ≥0∞ := ⨆ n : ℕ, ENNReal.ofReal (T.Zt n).L

/-- `F∞(t) = inf_n F*_{T_n}(t)`. -/
def Finf (t : ℝ) : ℝ := ⨅ n : ℕ, (T.Zt n).F t

theorem Linf_eq : T.Linf = infiniteEnvelope T.plus := by
  simp only [Linf, infiniteEnvelope, L_Zt]

theorem Finf_eq (t : ℝ) : T.Finf t = FInf T.plus t := by
  simp only [Finf, FInf, F_Zt]

/-- Shannon cost of `T` at all horizons, in bits. -/
def infiniteCostBits : ℝ≥0∞ := T.infiniteCost / natPerBit

/-- **Corollary 2 (envelope sandwich).** `L∞ ≤ C∞(T) ≤ L∞ + c⋆` (bits). -/
theorem envelope_sandwich :
    T.Linf ≤ T.infiniteCostBits ∧ T.infiniteCostBits ≤ T.Linf + ENNReal.ofReal shannonOverhead := by
  rw [Linf_eq, infiniteCostBits, infiniteCost_eq]
  exact infinite_envelope_sandwich T.plus

/-- **Corollary 2 (finite-entropy seeds).** An exact countable seed of finite entropy exists on `T`
iff `L∞ < ∞`; then one attains `C∞(T)` within `L∞ + c⋆`. -/
theorem finite_seed_iff :
    (∃ S : T.Seed, S.Exact ∧ S.entropy ≠ ∞) ↔ T.Linf ≠ ∞ := by
  constructor
  · rintro ⟨S, hS, hfin⟩
    have h1 : T.infiniteCost ≤ S.entropy := iInf_le_of_le ⟨S, hS⟩ le_rfl
    have h2 : T.infiniteCostBits ≠ ∞ := by
      unfold infiniteCostBits
      exact ENNReal.div_ne_top (ne_top_of_le_ne_top hfin h1) natPerBit_ne_zero
    exact ne_top_of_le_ne_top h2 T.envelope_sandwich.1
  · intro hL
    rw [Linf_eq] at hL
    obtain ⟨G, hG, _, hle⟩ := infinite_envelope_attained T.plus hL
    refine ⟨T.extSeed G, fun n => extSeed_exactTo (hG n), ?_⟩
    rw [extSeed_entropy]
    intro htop
    rw [htop, ENNReal.top_div_of_ne_top natPerBit_ne_top] at hle
    exact (ENNReal.add_lt_top.2 ⟨lt_top_iff_ne_top.2 hL, ENNReal.ofReal_lt_top⟩).ne (top_le_iff.1 hle)

theorem infiniteCost_attained_sandwich (hL : T.Linf ≠ ∞) :
    ∃ S : T.Seed, S.Exact ∧ S.entropy / natPerBit = T.infiniteCostBits ∧
      S.entropy / natPerBit ≤ T.Linf + ENNReal.ofReal shannonOverhead := by
  rw [Linf_eq] at hL ⊢
  obtain ⟨G, hG, he, hle⟩ := infinite_envelope_attained T.plus hL
  exact ⟨T.extSeed G, fun n => extSeed_exactTo (hG n),
    by rw [extSeed_entropy, he, infiniteCostBits, infiniteCost_eq]; rfl, hle⟩

/-! ### Atomic capacity -/

/-- The atomic capacity `q`, read off the spectrum of `T`: `q = sup_t F∞(t)`. -/
def q : ℝ := ⨆ t : ℝ, T.Finf t

theorem q_eq : T.q = atomQ T.plus := by
  rw [atomQ_eq_iSup_FInf]; simp only [q, Finf_eq]

/-- **Corollary 3 (spectral formula).** `F∞(t) → q` as `t → ∞`. -/
theorem tendsto_Finf : Tendsto T.Finf atTop (𝓝 T.q) := by
  have : T.Finf = FInf T.plus := funext T.Finf_eq
  rw [this, q_eq]; exact atomQ_eq_lim_FInf T.plus

instance : MeasurableSingletonClass T.Strat := inferInstance

theorem measurable_R : Measurable T.R := by
  refine measurable_pi_iff.2 fun p => ?_
  obtain ⟨g, hg⟩ := T.R_coord p
  have : (fun s => T.R s p) = fun s => g (s ⟨T.lift p.1, p.2⟩) := funext fun s => hg s
  rw [this]; exact (measurable_of_countable g).comp (measurable_pi_apply _)

theorem measurable_E : Measurable T.E := by
  refine measurable_pi_iff.2 fun p => ?_
  rcases T.E_coord p with ⟨c, hc⟩ | ⟨q, g, hg⟩
  · have : (fun s => T.E s p) = fun _ => c := funext fun s => hc s
    rw [this]; exact measurable_const
  · have : (fun s => T.E s p) = fun s => g (s q) := funext fun s => hg s
    rw [this]; exact (measurable_of_countable g).comp (measurable_pi_apply _)

theorem measurableSet_agree (h : List (ℕ × ℕ)) : MeasurableSet {s : T.Strat | T.Agree s h} := by
  have : {s : T.Strat | T.Agree s h} =
      ⋂ k ∈ Finset.range h.length, {s | T.Ok s (h.take k) (h.getD k (0, 0))} := by
    ext s; simp [Agree]
  rw [this]
  refine Finset.measurableSet_biInter _ fun k _ => ?_
  by_cases ha : (h.getD k (0, 0)).1 < T.nA (h.take k)
  · have : {s : T.Strat | T.Ok s (h.take k) (h.getD k (0, 0))} =
        (fun s : T.Strat => s ⟨h.take k, ⟨_, ha⟩⟩) ⁻¹' {y | y.val = (h.getD k (0, 0)).2} := by
      ext s
      simp only [Set.mem_setOf_eq, Set.mem_preimage, Ok]
      exact ⟨fun ⟨_, hv⟩ => hv, fun hv => ⟨ha, hv⟩⟩
    rw [this]
    exact (measurable_pi_apply _) (DiscreteMeasurableSpace.forall_measurableSet _)
  · have : {s : T.Strat | T.Ok s (h.take k) (h.getD k (0, 0))} = ∅ := by
      ext s
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, Ok]
      exact fun ⟨h1, _⟩ => ha h1
    rw [this]; exact MeasurableSet.empty

/-- An exact decoder for `T` gives an ordinary source for `T⁺` on the same space. -/
def ordOfDecoder {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} (D : T.Decoder Ω)
    (hD : ∀ n, D.ExactTo μ n) : OrdinarySource T.plus Ω μ where
  read n π ω := policyRead T.plus n π (T.R (D.D ω))
  measurable_fiber n π ℓ := by
    have hm : Measurable fun ω => T.R (D.D ω) := measurable_pi_iff.2 fun p => D.red.meas p
    have : (fun ω => policyRead T.plus n π (T.R (D.D ω))) ⁻¹' {ℓ} =
        (fun ω => T.R (D.D ω)) ⁻¹' (policyRead T.plus n π ⁻¹' {ℓ}) := rfl
    rw [this, policyRead_fiber]
    exact hm (measurable_cylinder _ _)
  exact_fiber n π ℓ := by
    have : (fun ω => policyRead T.plus n π (T.R (D.D ω))) ⁻¹' {ℓ} =
        {ω | iAgree T.plus (D.red.D ω) (truncPath T.plus n [] ℓ.val)} := by
      show (fun ω => T.R (D.D ω)) ⁻¹' (policyRead T.plus n π ⁻¹' {ℓ}) = _
      rw [policyRead_fiber]; rfl
    rw [this, (hD _).red μ _ le_rfl, pathMass_leaf]

/-- **Corollary 3 (converse).** Every exact causal decoder for `T`, on any probability space with
measurable singletons, has atomic mass at most `q`. -/
theorem atomic_upper {Ω : Type*} [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (D : T.Decoder Ω) (hD : ∀ n, D.ExactTo μ n) :
    atomicMass μ ≤ ENNReal.ofReal T.q := by
  rw [q_eq]; exact ordinary_atomic_upper μ (T.ordOfDecoder D hD)

/-- The identity decoder on reduced strategies. -/
def idDecP : T.DecoderP (IStrategy T.plus) where
  D := id
  meas p := measurable_pi_apply p

/-- **Corollary 3 (attainment on total strategies).** Some probability law on total response
strategies of `T` is exact at every history and has atomic mass exactly `q`. -/
theorem atomic_attained :
    ∃ μ : Measure T.Strat, IsProbabilityMeasure μ ∧
      (∀ h, μ {s | T.Agree s h} = ENNReal.ofReal (T.pathMass h)) ∧
      atomicMass μ = ENNReal.ofReal T.q := by
  obtain ⟨μp, hprob, hcyl, hatom⟩ := causal_atomic_capacity_attained T.plus
  have hE := T.measurable_E
  refine ⟨μp.map T.E, inferInstance, fun h => ?_, ?_⟩
  · rw [Measure.map_apply hE (T.measurableSet_agree h)]
    have hex : (T.idDecP).ExactTo μp h.length := fun h' _ => hcyl h'
    exact (hex.ext μp) h le_rfl
  · rw [q_eq, ← hatom]
    unfold atomicMass
    have hpre : ∀ s, T.E ⁻¹' {T.E s} = {s} := fun s => by
      ext x; simp [T.E_injective.eq_iff]
    have hsupp : Function.support (fun t => (μp.map T.E) {t}) ⊆ Set.range T.E := by
      intro t ht
      by_contra hn
      apply ht
      show (μp.map T.E) {t} = 0
      rw [Measure.map_apply hE (measurableSet_singleton t)]
      have : T.E ⁻¹' {t} = ∅ := by
        ext x; simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_empty_iff_false,
          iff_false]; exact fun e => hn ⟨x, e⟩
      rw [this, measure_empty]
    rw [← T.E_injective.tsum_eq hsupp]
    refine tsum_congr fun s => ?_
    rw [Measure.map_apply hE (measurableSet_singleton _), hpre]

/-- **Corollary 3 (countable seeds).** A countable seed exact at all horizons exists on `T`
iff `q = 1`. -/
theorem countable_seed_iff_q_one : (∃ S : T.Seed, S.Exact) ↔ T.q = 1 := by
  rw [q_eq, ← countable_seed_iff_atomQ_one]
  constructor
  · rintro ⟨S, hS⟩
    exact ⟨S.weight, fun i => T.R (S.strategy i), S.nonneg, S.mass,
      fun h => (hS h.length).red h le_rfl⟩
  · rintro ⟨w, s, hw, hm, hex⟩
    let G : Completion.Seed T.plus := ⟨w, hw, hm, s⟩
    exact ⟨T.extSeed G, fun n => extSeed_exactTo (fun h _ => hex h)⟩

/-! ### Rényi costs -/

open RenyiInf in
/-- Causal Rényi cost of `T` (bits), over countable seeds exact at all horizons. -/
def Calpha (α : ℝ) : ℝ≥0∞ := ⨅ S : {S : T.Seed // S.Exact}, H α S.1.weight

open RenyiInf in
def Cmin : ℝ≥0∞ := ⨅ S : {S : T.Seed // S.Exact}, Hinf S.1.weight

open RenyiInf in
theorem Calpha_eq (α : ℝ) : T.Calpha α = Cα T.plus α := by
  apply le_antisymm
  · exact le_iInf fun G => iInf_le_of_le ⟨T.extSeed G.1, fun n => extSeed_exactTo (G.2 n)⟩ le_rfl
  · exact le_iInf fun S => iInf_le_of_le ⟨S.1.red, fun n => (S.2 n).red⟩ le_rfl

open RenyiInf in
theorem Cmin_eq : T.Cmin = Cinf T.plus := by
  apply le_antisymm
  · exact le_iInf fun G => iInf_le_of_le ⟨T.extSeed G.1, fun n => extSeed_exactTo (G.2 n)⟩ le_rfl
  · exact le_iInf fun S => iInf_le_of_le ⟨S.1.red, fun n => (S.2 n).red⟩ le_rfl

open RenyiInf in
/-- **Corollary 4 (one seed for all orders).** If the reduced tree has a countable ordinary
exact source, one countable seed `S` on `T`, exact at all horizons, satisfies for every `α > 0`
`R_α(Z) ≤ O_α ≤ C_α(T) ≤ H_α(S) ≤ R_α(Z) + d_α`, and its min-entropy attains both optima. -/
theorem one_seed_all_orders (hU : Nonempty (OrdSource T.plus)) :
    ∃ S : T.Seed, S.Exact ∧
      (∀ α : ℝ, 0 < α →
        RZmeas T.plus α ≤ Oα T.plus α ∧ Oα T.plus α ≤ T.Calpha α ∧ T.Calpha α ≤ H α S.weight ∧
          H α S.weight ≤ RZmeas T.plus α + ENNReal.ofReal (dA α)) ∧
      Hinf S.weight = T.Cmin ∧ T.Cmin = Oinf T.plus := by
  obtain ⟨G, hG, hall, h1, h2⟩ := one_seed_all_orders_meas T.plus hU
  refine ⟨T.extSeed G, fun n => extSeed_exactTo (hG n), fun α hα => ?_, ?_, ?_⟩
  · rw [Calpha_eq]; exact hall α hα
  · rw [Cmin_eq]; exact h1
  · rw [Cmin_eq]; exact h2

end NNTree
end CausalSpectrum.ZeroBranch
